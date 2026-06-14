#pragma GCC optimize("O3")
#pragma GCC optimize("unroll-loops")
#pragma GCC target("avx2,bmi,bmi2,popcnt,lzcnt")

#include <cstdio>
#include <cstdint>
#include <vector>
#include <string>
#include <algorithm>
#include <chrono>
#include <ctime>
#include <deque>
#include <unistd.h>

using namespace std;

static const double kBudget = 9.5;
static const int kHashBits = 21, kRouteKeep = 8;
static const long kNodeCap = 20000000;
static const int stepRow[4] = {-1, 1, 0, 0}, stepCol[4] = {0, 0, -1, 1};
static const int bounceA[4] = {3, 2, 1, 0}, bounceB[4] = {2, 3, 0, 1};
static int W, H, L, N, catN, rayCap;
static int rayTagN = 0, onRayN = 0, litTagN = 0, litTagCur = 0, dirBitsN = 0,
           tailTagN = 0, tapTagN = 0, qTagN = 0, freshTagN = 0, hitTagN = 0, bestLit = -1;
static long nodes = 0;
static size_t hashMask = 0, hashFill = 0;
static bool solved = false, hashSat = false, exFull = false;
static double deadline = 0.0;
static vector<uint8_t> isWall, isFree, dirBits;
static vector<int> catId, catCell, emR, emC, emD, rayTag, onRay, litTag, dirBitsTag,
           tailTag, rayPath, tapTag, qDist, qDistTag, qDoneTag, qPrev,
           curPos, winPos, bestPos, freshTag, hitTag;
static vector<int8_t> qMove, cellMir, curMc, winMc, bestMc;
static vector<uint64_t> zob, hashSet;
static chrono::steady_clock::time_point wall0;
static clock_t cpu0;
static inline double secs() {
    double w = chrono::duration<double>(chrono::steady_clock::now() - wall0).count();
    double c = double(clock() - cpu0) / (double)CLOCKS_PER_SEC;
    return w > c ? w : c;
}

static int spanN = 0;
static int traceAll(vector<int>& seeds, bool fill_dmask) {
    seeds.clear();
    int sep = ++onRayN;
    int cep = ++litTagN;
    int vce = ++hitTagN;
    int dep = 0, safep = 0;
    if (fill_dmask) { dep = ++dirBitsN; safep = ++tailTagN; }
    litTagCur = cep;
    int cnt = 0; spanN = 0;
    for (size_t s = 0; s < emR.size(); ++s) {
        if ((s & 63) == 0 && secs() > deadline) return cnt;
        int ep = ++rayTagN;
        int r = emR[s], c = emC[s], d = emD[s];
        if (fill_dmask) rayPath.clear();
        for (int step = 0; step < rayCap; ++step) {
            if ((step & 8191) == 0 && secs() > deadline) return cnt;
            r += stepRow[d]; c += stepCol[d];
            if (r < 0 || r >= H || c < 0 || c >= W) break;
            int pos = r * W + c;
            if (isWall[pos]) break;
            int st = pos * 4 + d;
            if (rayTag[st] == ep) break;
            rayTag[st] = ep;
            if (hitTag[pos] != vce) { hitTag[pos] = vce; ++spanN; }
            if (onRay[st] != sep) { onRay[st] = sep; seeds.push_back(st); }
            if (fill_dmask) {
                if (dirBitsTag[pos] != dep) { dirBitsTag[pos] = dep; dirBits[pos] = 0; }
                dirBits[pos] |= (uint8_t)(1 << d);
                rayPath.push_back(st);
            }
            int ci = catId[pos];
            if (ci >= 0 && litTag[ci] != cep) { litTag[ci] = cep; ++cnt; }
            int8_t m = cellMir[pos];
            if (m) d = (m == 1) ? bounceA[d] : bounceB[d];
        }
        if (fill_dmask) {

            bool seen_cat = false;
            for (int i = (int)rayPath.size() - 1; i >= 0; --i) {
                int st = rayPath[i];
                if (!seen_cat) tailTag[st] = safep;
                if (catId[st >> 2] >= 0) seen_cat = true;
            }
        }
    }
    return cnt;
}

static deque<int> q;
static void bfs(const vector<int>& seeds, bool safe_only) {
    int ep = ++qTagN;
    q.clear();
    for (int st : seeds) {
        if (safe_only && tailTag[st] != tailTagN) continue;
        qDist[st] = 0; qDistTag[st] = ep; qPrev[st] = -1; qMove[st] = -1;
        q.push_back(st);
    }
    while (!q.empty()) {
        int st = q.front(); q.pop_front();
        if (qDoneTag[st] == ep) continue;
        qDoneTag[st] = ep;
        int dcur = qDist[st];
        int pos = st >> 2, d = st & 3;
        int r = pos / W, c = pos % W;

        int nr = r + stepRow[d], nc = c + stepCol[d];
        if (nr >= 0 && nr < H && nc >= 0 && nc < W) {
            int np = nr * W + nc;
            if (!isWall[np]) {
                int nd = cellMir[np] ? (cellMir[np] == 1 ? bounceA[d] : bounceB[d]) : d;
                int nst = np * 4 + nd;
                if (qDistTag[nst] != ep || qDist[nst] > dcur) {
                    qDist[nst] = dcur; qDistTag[nst] = ep; qPrev[nst] = st; qMove[nst] = 0;
                    q.push_front(nst);
                }
            }
        }

        if (isFree[pos] && cellMir[pos] == 0) {
            for (int8_t t = 1; t <= 2; ++t) {
                int nd = (t == 1) ? bounceA[d] : bounceB[d];
                int nst = pos * 4 + nd;
                if (qDistTag[nst] != ep || qDist[nst] > dcur + 1) {
                    qDist[nst] = dcur + 1; qDistTag[nst] = ep; qPrev[nst] = st; qMove[nst] = t;
                    q.push_back(nst);
                }
            }
        }
    }
}

static bool routeFrom(int endst, vector<pair<int,int8_t>>& out) {
    out.clear();
    int s = endst, guard = 0, lim = 4 * N + 16;
    while (s != -1 && qMove[s] != -1 && guard++ < lim) {
        int8_t a = qMove[s];
        if (a != 0) out.push_back({s >> 2, a});
        s = qPrev[s];
    }

    for (size_t i = 0; i < out.size(); ++i)
        for (size_t j = i + 1; j < out.size(); ++j)
            if (out[i].first == out[j].first) return false;
    return !out.empty();
}

static inline bool hashAdd(uint64_t k) {
    if (!k) k = 0x1234567;
    size_t i = (size_t)(k * 0x9E3779B97F4A7C15ULL >> 40) & hashMask;
    while (hashSet[i]) { if (hashSet[i] == k) return false; i = (i + 1) & hashMask; }
    hashSet[i] = k;
    if (++hashFill * 10 > (hashMask + 1) * 7) hashSat = true;
    return true;
}

static inline uint8_t dirsAt(int pos) {
    return (dirBitsTag[pos] == dirBitsN) ? dirBits[pos] : 0;
}

static bool segClear(int r0, int c0, int r1, int c1) {
    int dr = (r1 > r0) - (r1 < r0);
    int dc = (c1 > c0) - (c1 < c0);
    int r = r0 + dr, c = c0 + dc;
    while (r != r1 || c != c1) {
        int pos = r * W + c;
        if (isWall[pos] || cellMir[pos]) return false;
        r += dr; c += dc;
    }
    return true;
}

struct Tap { int pos; int8_t mc; int pri; };

static inline bool tapTail(int mp, int bd) {
    return tailTag[mp * 4 + bd] == tailTagN;
}

static void on019Taps(int cp, vector<Tap>& out) {
    int cr = cp / W, cc = cp % W;

    for (int mr = 0; mr < H; ++mr) {
        if (mr == cr) continue;
        int mp = mr * W + cc;
        if (!isFree[mp] || cellMir[mp]) continue;
        uint8_t dm = dirsAt(mp);
        if (!(dm & ((1 << 2) | (1 << 3)))) continue;
        if (!segClear(mr, cc, cr, cc)) continue;
        bool down = (mr < cr);
        if (dm & (1 << 3)) out.push_back({mp, (int8_t)(down ? 2 : 1), tapTail(mp, 3) ? 0 : 1});
        if (dm & (1 << 2)) out.push_back({mp, (int8_t)(down ? 1 : 2), tapTail(mp, 2) ? 0 : 1});
    }

    for (int mc = 0; mc < W; ++mc) {
        if (mc == cc) continue;
        int mp = cr * W + mc;
        if (!isFree[mp] || cellMir[mp]) continue;
        uint8_t dm = dirsAt(mp);
        if (!(dm & ((1 << 0) | (1 << 1)))) continue;
        if (!segClear(cr, mc, cr, cc)) continue;
        bool right = (mc < cc);
        if (dm & (1 << 0)) out.push_back({mp, (int8_t)(right ? 1 : 2), tapTail(mp, 0) ? 0 : 1});
        if (dm & (1 << 1)) out.push_back({mp, (int8_t)(right ? 2 : 1), tapTail(mp, 1) ? 0 : 1});
    }
}

struct RouteOpt { vector<pair<int,int8_t>> cellMir; int lit; int reach; };

static const int EVAL_CAP = 40;

static int lineLB(int cep);
static bool wideMode = false;
static uint32_t permSeed = 0;
static inline uint32_t permHash(int x) {
    uint32_t h = (uint32_t)x * 2654435761u ^ permSeed;
    h ^= h >> 15; h *= 2246822519u; h ^= h >> 13; return h;
}

static bool dfs(int used, uint64_t hash) {
    if (solved || ++nodes > kNodeCap || secs() > deadline) return false;
    vector<int> seeds;
    int cnt = traceAll(seeds, true);
    if (cnt == catN) {
        winPos = curPos; winMc = curMc; solved = true; return true;
    }
    if (cnt > bestLit) { bestLit = cnt; bestPos = curPos; bestMc = curMc; }
    if (used >= L || secs() > deadline) return false;
    if (used + lineLB(litTagCur) > L) return false;

    vector<vector<pair<int,int8_t>>> cand;
    vector<int> cand_pri;
    int tep = ++tapTagN;
    int ep = 0;

    if (!wideMode) {

        int target = -1, tcost = 0x3fffffff;
        for (int safe_only = 1; safe_only >= 0 && target < 0; --safe_only) {
            bfs(seeds, safe_only);
            ep = qTagN;
            for (int ci = 0; ci < catN; ++ci) {
                if (litTag[ci] == litTagCur) continue;
                int cp = catCell[ci], best = 0x3fffffff;
                for (int d = 0; d < 4; ++d) {
                    int st = cp * 4 + d;
                    if (qDistTag[st] == ep && qDist[st] < best) best = qDist[st];
                }
                if (best == 0x3fffffff) continue;
                if (best < tcost) { tcost = best; target = ci; }
            }
        }
        if (target < 0 || used + tcost > L) return false;
        int cp = catCell[target];
        vector<Tap> taps;
        if (tcost <= 1) on019Taps(cp, taps);
        stable_sort(taps.begin(), taps.end(),
                    [](const Tap& a, const Tap& b) { return a.pri < b.pri; });
        for (const Tap& t : taps) { cand.push_back({{t.pos, t.mc}}); cand_pri.push_back(t.pri); }
        for (int extra = 0; extra <= 2; ++extra) {
            int want = tcost + extra;
            if (used + want > L) break;
            bool any = false;
            for (int d = 0; d < 4; ++d) {
                int st = cp * 4 + d;
                if (qDistTag[st] != ep || qDist[st] != want) continue;
                vector<pair<int,int8_t>> rm;
                if (routeFrom(st, rm)) { cand.push_back(move(rm)); cand_pri.push_back(2); any = true; }
            }
            if (any && extra == 0 && !taps.empty()) break;
        }
    } else {

        bfs(seeds, false);
        ep = qTagN;
        vector<Tap> taps;
        for (int ci = 0; ci < catN && (int)cand.size() + (int)taps.size() < 400; ++ci) {
            if ((ci & 63) == 0 && secs() > deadline) return false;
            if (litTag[ci] == litTagCur) continue;
            int cp = catCell[ci], best = 0x3fffffff;
            for (int d = 0; d < 4; ++d) {
                int st = cp * 4 + d;
                if (qDistTag[st] == ep && qDist[st] < best) best = qDist[st];
            }
            if (best == 0x3fffffff || used + best > L) continue;
            if (best <= 1) on019Taps(cp, taps);

            for (int d = 0; d < 4; ++d) {
                int st = cp * 4 + d;
                if (qDistTag[st] != ep || qDist[st] != best) continue;
                vector<pair<int,int8_t>> rm;
                if (routeFrom(st, rm)) { cand.push_back(move(rm)); cand_pri.push_back(2); }
            }
        }
        for (const Tap& t : taps) {
            int key = t.pos * 2 + (t.mc - 1);
            if (tapTag[key] == tep) continue;
            tapTag[key] = tep;
            cand.push_back({{t.pos, t.mc}});
            cand_pri.push_back(t.pri);
        }
    }
    if (cand.empty()) return false;

    vector<int> order(cand.size());
    for (size_t i = 0; i < order.size(); ++i) order[i] = (int)i;
    stable_sort(order.begin(), order.end(),
                [&](int a, int b) { return cand_pri[a] < cand_pri[b]; });

    vector<RouteOpt> routes;
    for (int idx : order) {
        if ((int)routes.size() >= EVAL_CAP) break;
        if (secs() > deadline) return false;
        auto& rm = cand[idx];
        if (rm.empty() || used + (int)rm.size() > L) continue;
        for (auto& pr : rm) cellMir[pr.first] = pr.second;
        vector<int> tmp;
        int lit = traceAll(tmp, false);
        int reach = spanN;
        if (lit > bestLit) {
            bestLit = lit; bestPos = curPos; bestMc = curMc;
            for (auto& pr : rm) { bestPos.push_back(pr.first); bestMc.push_back(pr.second); }
        }
        for (auto& pr : rm) cellMir[pr.first] = 0;
        routes.push_back({rm, lit, reach});
    }
    if (routes.empty()) return false;

    stable_sort(routes.begin(), routes.end(), [](const RouteOpt& a, const RouteOpt& b) {
        if (a.lit != b.lit) return a.lit > b.lit;
        if (a.cellMir.size() != b.cellMir.size()) return a.cellMir.size() < b.cellMir.size();
        return permHash(a.cellMir[0].first) < permHash(b.cellMir[0].first);
    });
    if ((int)routes.size() > kRouteKeep) routes.resize(kRouteKeep);

    for (auto& rt : routes) {
        if (solved || secs() > deadline) return false;
        uint64_t h2 = hash;
        for (auto& pr : rt.cellMir) h2 ^= zob[(size_t)pr.first * 3 + pr.second];
        if (!hashAdd(h2)) continue;
        for (auto& pr : rt.cellMir) {
            cellMir[pr.first] = pr.second;
            curPos.push_back(pr.first); curMc.push_back(pr.second);
        }
        bool ok = dfs(used + (int)rt.cellMir.size(), h2);
        for (size_t i = 0; i < rt.cellMir.size(); ++i) {
            curPos.pop_back(); curMc.pop_back();
            cellMir[rt.cellMir[i].first] = 0;
        }
        if (ok) return true;
    }
    return false;
}

static int exTrace(vector<int>& cells, int target_pos) {
    int cep = ++litTagN;
    int ce = ++freshTagN;
    cells.clear();
    int cnt = 0;
    for (size_t s = 0; s < emR.size(); ++s) {
        if ((s & 63) == 0 && secs() > deadline) return cnt;
        int ep = ++rayTagN;
        int r = emR[s], c = emC[s], d = emD[s];
        bool past_last = (target_pos < 0);
        for (int step = 0; step < rayCap; ++step) {
            if ((step & 8191) == 0 && secs() > deadline) return cnt;
            r += stepRow[d]; c += stepCol[d];
            if (r < 0 || r >= H || c < 0 || c >= W) break;
            int pos = r * W + c;
            if (isWall[pos]) break;
            int st = pos * 4 + d;
            if (rayTag[st] == ep) break;
            rayTag[st] = ep;
            int ci = catId[pos];
            if (ci >= 0 && litTag[ci] != cep) { litTag[ci] = cep; ++cnt; }
            int8_t m = cellMir[pos];
            if (m) {
                if (pos == target_pos) past_last = true;
                d = (m == 1) ? bounceA[d] : bounceB[d];
            } else if (isFree[pos] && past_last && freshTag[pos] != ce) {
                freshTag[pos] = ce;
                cells.push_back(pos);
            }
        }
    }
    return cnt;
}

static int exLit(int& out_reach) {
    int cep = ++litTagN;
    int vce = ++hitTagN;
    int cnt = 0, reach = 0;
    for (size_t s = 0; s < emR.size(); ++s) {
        if ((s & 63) == 0 && secs() > deadline) { out_reach = reach; return cnt; }
        int ep = ++rayTagN;
        int r = emR[s], c = emC[s], d = emD[s];
        for (int step = 0; step < rayCap; ++step) {
            if ((step & 8191) == 0 && secs() > deadline) { out_reach = reach; return cnt; }
            r += stepRow[d]; c += stepCol[d];
            if (r < 0 || r >= H || c < 0 || c >= W) break;
            int pos = r * W + c;
            if (isWall[pos]) break;
            int st = pos * 4 + d;
            if (rayTag[st] == ep) break;
            rayTag[st] = ep;
            if (hitTag[pos] != vce) { hitTag[pos] = vce; ++reach; }
            int ci = catId[pos];
            if (ci >= 0 && litTag[ci] != cep) { litTag[ci] = cep; ++cnt; }
            int8_t m = cellMir[pos];
            if (m) d = (m == 1) ? bounceA[d] : bounceB[d];
        }
    }
    out_reach = reach;
    return cnt;
}

static vector<vector<int>> lbAdj;
static vector<int> lbMatch;
static vector<char> lbUsed;
static bool lbAug(int r) {
    for (int col : lbAdj[r]) {
        if (!lbUsed[col]) {
            lbUsed[col] = 1;
            if (lbMatch[col] < 0 || lbAug(lbMatch[col])) { lbMatch[col] = r; return true; }
        }
    }
    return false;
}
static int lineLB(int cep) {
    for (int r = 0; r < H; ++r) lbAdj[r].clear();
    for (int ci = 0; ci < catN; ++ci)
        if (litTag[ci] != cep) lbAdj[catCell[ci] / W].push_back(catCell[ci] % W);
    for (int c = 0; c < W; ++c) lbMatch[c] = -1;
    int m = 0;
    for (int r = 0; r < H; ++r) {
        if (lbAdj[r].empty()) continue;
        for (int c = 0; c < W; ++c) lbUsed[c] = 0;
        if (lbAug(r)) ++m;
    }
    return m;
}

struct ExTap { int cnt, reach, pos; int8_t mc; };
static void exSearch(int used, uint64_t hash) {
    if (solved || hashSat || ++nodes > kNodeCap || secs() > deadline) return;
    vector<int> cells;
    int target = (exFull || curPos.empty()) ? -1 : curPos.back();
    int cnt = exTrace(cells, target);
    if (cnt == catN) { winPos = curPos; winMc = curMc; solved = true; return; }
    if (cnt > bestLit) { bestLit = cnt; bestPos = curPos; bestMc = curMc; }
    if (used >= L || cells.empty()) return;
    if (used + lineLB(litTagN) > L) return;

    if (!exFull) {
        vector<ExTap> cs;
        cs.reserve(cells.size() * 2);
        int ck = 0;
        for (int pos : cells) {
            if ((ck++ & 7) == 0 && secs() > deadline) return;
            for (int8_t t = 1; t <= 2; ++t) {
                cellMir[pos] = t;
                int reach; int cc = exLit(reach);
                if (cc > bestLit) {
                    bestLit = cc; bestPos = curPos; bestMc = curMc;
                    bestPos.push_back(pos); bestMc.push_back(t);
                }
                cellMir[pos] = 0;
                cs.push_back({cc, reach, pos, t});
            }
        }
        sort(cs.begin(), cs.end(), [](const ExTap& a, const ExTap& b) {
            if (a.cnt != b.cnt) return a.cnt > b.cnt;
            return a.reach > b.reach;
        });
        for (const ExTap& cd : cs) {
            if (solved || hashSat || secs() > deadline) return;
            uint64_t h2 = hash ^ zob[(size_t)cd.pos * 3 + cd.mc];
            if (!hashAdd(h2)) continue;
            cellMir[cd.pos] = cd.mc;
            curPos.push_back(cd.pos); curMc.push_back(cd.mc);
            if (cd.cnt == catN) { winPos = curPos; winMc = curMc; solved = true; }
            else exSearch(used + 1, h2);
            curPos.pop_back(); curMc.pop_back();
            cellMir[cd.pos] = 0;
            if (solved) return;
        }
    } else {
        int ck = 0;
        for (int pos : cells) {
            if ((ck++ & 7) == 0 && secs() > deadline) return;
            for (int8_t t = 1; t <= 2; ++t) {
                uint64_t h2 = hash ^ zob[(size_t)pos * 3 + t];
                if (!hashAdd(h2)) continue;
                cellMir[pos] = t;
                curPos.push_back(pos); curMc.push_back(t);
                exSearch(used + 1, h2);
                curPos.pop_back(); curMc.pop_back();
                cellMir[pos] = 0;
                if (solved || hashSat) return;
            }
        }
    }
}

static void exSolve() {
    lbAdj.assign(H, {}); lbMatch.assign(W, -1); lbUsed.assign(W, 0);
    freshTag.assign(N, 0);
    hitTag.assign(N, 0);
    for (int pass = 0; pass < 2 && !solved && secs() < deadline; ++pass) {
        exFull = (pass == 1);
        std::fill(hashSet.begin(), hashSet.end(), (uint64_t)0);
        hashFill = 0; hashSat = false;
        std::fill(cellMir.begin(), cellMir.end(), (int8_t)0);
        curPos.clear(); curMc.clear();
        exSearch(0, 0);
    }
}

static int firstCat = -1;

static void greedyFill() {
    vector<int> seeds;
    while (!solved && secs() <= deadline && (int)curPos.size() < L) {
        int cnt = traceAll(seeds, true);
        if (cnt > bestLit) { bestLit = cnt; bestPos = curPos; bestMc = curMc; }
        if (cnt == catN) { winPos = curPos; winMc = curMc; solved = true; return; }

        int ep = 0, target = -1, tcost = 0x3fffffff;
        for (int so = 1; so >= 0 && target < 0; --so) {
            bfs(seeds, so); ep = qTagN;

            if (firstCat >= 0 && litTag[firstCat] != litTagCur) {
                int cp = catCell[firstCat], b = 0x3fffffff;
                for (int d = 0; d < 4; ++d) { int st = cp * 4 + d; if (qDistTag[st] == ep && qDist[st] < b) b = qDist[st]; }
                if (b != 0x3fffffff) { tcost = b; target = firstCat; break; }
            }
            for (int ci = 0; ci < catN; ++ci) {
                if (litTag[ci] == litTagCur) continue;
                int cp = catCell[ci], b = 0x3fffffff;
                for (int d = 0; d < 4; ++d) { int st = cp * 4 + d; if (qDistTag[st] == ep && qDist[st] < b) b = qDist[st]; }
                if (b == 0x3fffffff) continue;
                if (b < tcost) { tcost = b; target = ci; }
            }
        }
        int used = (int)curPos.size();
        if (target < 0 || used + tcost > L) return;

        int cp = catCell[target];
        vector<vector<pair<int,int8_t>>> cand;
        vector<Tap> taps;
        if (tcost <= 1) on019Taps(cp, taps);
        for (const Tap& t : taps) cand.push_back({{t.pos, t.mc}});
        for (int extra = 0; extra <= 2; ++extra) {
            int want = tcost + extra;
            if (used + want > L) break;
            bool any = false;
            for (int d = 0; d < 4; ++d) {
                int st = cp * 4 + d;
                if (qDistTag[st] != ep || qDist[st] != want) continue;
                vector<pair<int,int8_t>> rm;
                if (routeFrom(st, rm)) { cand.push_back(move(rm)); any = true; }
            }
            if (any && extra == 0 && !taps.empty()) break;
        }
        if (cand.empty()) return;

        int bestlit = -1; int bi = -1; uint32_t bh = 0;
        for (int i = 0; i < (int)cand.size(); ++i) {
            auto& rm = cand[i];
            if (rm.empty() || used + (int)rm.size() > L) continue;
            for (auto& pr : rm) cellMir[pr.first] = pr.second;
            vector<int> tmp; int lit = traceAll(tmp, false);
            for (auto& pr : rm) cellMir[pr.first] = 0;
            uint32_t h = permHash(rm[0].first);
            if (lit > bestlit || (lit == bestlit && h < bh)) { bestlit = lit; bi = i; bh = h; }
        }
        if (bi < 0 || bestlit <= cnt) return;
        for (auto& pr : cand[bi]) { cellMir[pr.first] = pr.second; curPos.push_back(pr.first); curMc.push_back(pr.second); }
    }
}

static void greedyFrom(bool from_best) {
    std::fill(cellMir.begin(), cellMir.end(), (int8_t)0);
    curPos.clear(); curMc.clear();
    if (from_best) {
        for (size_t i = 0; i < bestPos.size(); ++i) cellMir[bestPos[i]] = bestMc[i];
        curPos = bestPos; curMc = bestMc;
    }
    greedyFill();
}

static void lnsFix() {
    if (solved || bestPos.empty() || bestLit >= catN) return;
    vector<int> seeds, unlit;

    vector<int> cur_pos = bestPos; vector<int8_t> cur_mc = bestMc;
    int cur_cnt = bestLit;
    for (uint32_t it = 1; !solved && secs() < deadline; ++it) {
        if ((it & 63) == 0) { cur_pos = bestPos; cur_mc = bestMc; cur_cnt = bestLit; }
        std::fill(cellMir.begin(), cellMir.end(), (int8_t)0);
        for (size_t i = 0; i < cur_pos.size(); ++i) cellMir[cur_pos[i]] = cur_mc[i];
        curPos = cur_pos; curMc = cur_mc;
        traceAll(seeds, false);
        unlit.clear();
        for (int ci = 0; ci < catN; ++ci) if (litTag[ci] != litTagCur) unlit.push_back(catCell[ci]);
        if (unlit.empty()) break;
        int tgt = unlit[(it * 2654435761u) % unlit.size()];
        int tr = tgt / W, tc = tgt % W;
        int R = 3 + (int)(it % 10);
        vector<int> np; vector<int8_t> nm;
        for (size_t i = 0; i < curPos.size(); ++i) {
            int mr = curPos[i] / W, mc = curPos[i] % W;
            int cheb = std::max(abs(mr - tr), abs(mc - tc));
            if (cheb <= R) cellMir[curPos[i]] = 0;
            else { np.push_back(curPos[i]); nm.push_back(curMc[i]); }
        }
        if (np.size() == curPos.size()) continue;
        curPos.swap(np); curMc.swap(nm);
        permSeed = it * 40503u + 12345u;
        firstCat = catId[tgt];
        greedyFill();
        firstCat = -1;
        int w = traceAll(seeds, false);
        if (w >= cur_cnt) { cur_pos = curPos; cur_mc = curMc; cur_cnt = w; }
    }
    permSeed = 0;
}

static int dropCap = 200;

static int shareCap = 0x7fffffff;
static bool snakeOne(size_t si, vector<int>& seeds, vector<int>& tmp) {
    int sr = emR[si], sc = emC[si], sd = emD[si];
    bool progressed = false;
    int baseline = -1;
    while (!solved && secs() <= deadline && (int)curPos.size() + 2 <= L) {
        int cnt = traceAll(seeds, false);
        if (baseline < 0) baseline = cnt;
        if (cnt > bestLit) { bestLit = cnt; bestPos = curPos; bestMc = curMc; }
        if (cnt == catN) { winPos = curPos; winMc = curMc; solved = true; return progressed; }
        if (cnt - baseline >= shareCap) break;

        int er = -1, ec = -1, ed = -1;
        int ep = ++rayTagN; int r = sr, c = sc, d = sd;
        for (int step = 0; step < rayCap; ++step) {
            int nr = r + stepRow[d], nc = c + stepCol[d];
            if (nr < 0 || nr >= H || nc < 0 || nc >= W || isWall[nr * W + nc]) { er = r; ec = c; ed = d; break; }
            r = nr; c = nc; int sst = (r * W + c) * 4 + d;
            if (rayTag[sst] == ep) { er = r; ec = c; ed = d; break; }
            rayTag[sst] = ep;
            int8_t m = cellMir[r * W + c];
            if (m) d = (m == 1) ? bounceA[d] : bounceB[d];
        }
        if (er < 0) break;
        int expos = er * W + ec;
        if (!isFree[expos] || cellMir[expos]) break;
        int bestscore = 0, bp1 = -1, bp2 = -1; int8_t bt1 = 0, bt2 = 0;
        for (int8_t t1 = 1; t1 <= 2; ++t1) {
            cellMir[expos] = t1;
            int nd = (t1 == 1) ? bounceA[ed] : bounceB[ed];
            { int lit = traceAll(tmp, false); if (lit - cnt > bestscore) { bestscore = lit - cnt; bp1 = expos; bt1 = t1; bp2 = -1; } }
            int ep2 = ++rayTagN; int rr = er, cc = ec, dd = nd, scan = 0, colcats = 0;
            for (int step = 0; step < rayCap && scan < dropCap; ++step) {
                int nr = rr + stepRow[dd], nc = cc + stepCol[dd];
                if (nr < 0 || nr >= H || nc < 0 || nc >= W || isWall[nr * W + nc]) break;
                rr = nr; cc = nc; int pos = rr * W + cc; int sst = pos * 4 + dd;
                if (rayTag[sst] == ep2) break; rayTag[sst] = ep2;
                if (catId[pos] >= 0) ++colcats;

                int8_t m = cellMir[pos];
                if (m) { dd = (m == 1) ? bounceA[dd] : bounceB[dd]; continue; }
                if (isFree[pos]) {
                    ++scan;
                    for (int8_t t2 = 1; t2 <= 2; ++t2) {
                        cellMir[pos] = t2; int lit = traceAll(tmp, false); cellMir[pos] = 0;

                        int score = (lit - cnt) - colcats - scan;
                        if (lit > cnt && score > bestscore) { bestscore = score; bp1 = expos; bt1 = t1; bp2 = pos; bt2 = t2; }
                    }
                }
            }
            cellMir[expos] = 0;
        }
        if (bp1 < 0) break;
        cellMir[bp1] = bt1; curPos.push_back(bp1); curMc.push_back(bt1);
        if (bp2 >= 0) { cellMir[bp2] = bt2; curPos.push_back(bp2); curMc.push_back(bt2); }
        progressed = true;
    }
    return progressed;
}

static void snakeFill() {
    if (emR.empty()) return;
    std::fill(cellMir.begin(), cellMir.end(), (int8_t)0);
    curPos.clear(); curMc.clear();
    vector<int> seeds, tmp;
    dropCap = (N <= 6000) ? 200 : 90;
    int K = (int)emR.size();
    for (int round = 0; round < 5 && !solved && secs() <= deadline; ++round) {
        bool any = false;
        for (size_t si = 0; si < emR.size() && !solved; ++si) {

            shareCap = (round == 0 && K > 1) ? (catN + K - 1) / K : 0x7fffffff;
            any |= snakeOne(si, seeds, tmp);
        }
        shareCap = 0x7fffffff;
        if (!any) break;
    }

    {
        int cnt = traceAll(seeds, false);
        if (cnt > bestLit) { bestLit = cnt; bestPos = curPos; bestMc = curMc; }
        if (cnt == catN) { winPos = curPos; winMc = curMc; solved = true; }
    }
}

static const int kBeamW = 1000;
static const int kOver = 4;
static int bsR, bsC, bsD, catWords;
static vector<int8_t> chainMir;
static vector<int>    chainTag;
static int            chainN = 0;
static vector<int>    linkPrev, linkPos;
static vector<int8_t> linkMc;
static vector<int>    nodePrev, nodeMir, nodeLit, nodeLast;

struct BeamStep { int pl, sid, prev_m, nm, pos; int8_t mc; };
static vector<BeamStep> expBuf;

static inline int chainBuild(int chain_head) {
    int t = ++chainN, cur = chain_head;
    while (cur >= 0) { chainMir[linkPos[cur]] = linkMc[cur]; chainTag[linkPos[cur]] = t; cur = linkPrev[cur]; }
    return t;
}

static inline bool chainTrace(int grid_tag, uint64_t* lit, int& out_cnt) {
    int ep = ++rayTagN;
    for (int w = 0; w < catWords; ++w) lit[w] = 0;
    int r = bsR, c = bsC, d = bsD, cnt = 0;
    for (int step = 0; step < rayCap; ++step) {
        if ((step & 8191) == 0 && secs() > deadline) { out_cnt = cnt; return true; }
        r += stepRow[d]; c += stepCol[d];
        if (r < 0 || r >= H || c < 0 || c >= W) { out_cnt = cnt; return false; }
        int pos = r * W + c;
        if (isWall[pos]) { out_cnt = cnt; return false; }
        int st = pos * 4 + d;
        if (rayTag[st] == ep) { out_cnt = cnt; return true; }
        rayTag[st] = ep;
        int ci = catId[pos];
        if (ci >= 0) { uint64_t& wb = lit[ci >> 6]; uint64_t b = 1ULL << (ci & 63); if (!(wb & b)) { wb |= b; ++cnt; } }
        if (chainTag[pos] == grid_tag) d = (chainMir[pos] == 1) ? bounceA[d] : bounceB[d];
    }
    out_cnt = cnt; return true;
}
static inline void chainExpand(int sid, int prev_m, int nm, int grid_tag, int target_pos, int parent_lit) {
    int ep = ++rayTagN, ce = ++freshTagN;
    int r = bsR, c = bsC, d = bsD;
    bool past_last = (target_pos < 0);
    for (int step = 0; step < rayCap; ++step) {
        r += stepRow[d]; c += stepCol[d];
        if (r < 0 || r >= H || c < 0 || c >= W) break;
        int pos = r * W + c;
        if (isWall[pos]) break;
        int st = pos * 4 + d;
        if (rayTag[st] == ep) break;
        rayTag[st] = ep;
        if (chainTag[pos] == grid_tag) {
            if (pos == target_pos) past_last = true;
            d = (chainMir[pos] == 1) ? bounceA[d] : bounceB[d];
            continue;
        }
        if (isFree[pos] && past_last && freshTag[pos] != ce) {
            freshTag[pos] = ce;
            expBuf.push_back({parent_lit, sid, prev_m, nm, pos, 1});
            expBuf.push_back({parent_lit, sid, prev_m, nm, pos, 2});
        }
    }
}
static void chainOut(int sid, vector<int>& op, vector<int8_t>& om) {
    op.clear(); om.clear();
    int cur = nodePrev[sid];
    while (cur >= 0) { op.push_back(linkPos[cur]); om.push_back(linkMc[cur]); cur = linkPrev[cur]; }
}

static void beamFill() {
    linkPrev.clear(); linkPos.clear(); linkMc.clear();
    nodePrev.clear(); nodeMir.clear(); nodeLit.clear(); nodeLast.clear();
    int cap = kOver * kBeamW;
    vector<uint64_t> tmp(catWords);

    int gt = chainBuild(-1);
    int rcnt; chainTrace(gt, tmp.data(), rcnt);
    nodePrev.push_back(-1); nodeMir.push_back(0); nodeLit.push_back(rcnt); nodeLast.push_back(-1);

    auto record = [&](int sid) {
        if (nodeLit[sid] > bestLit) { bestLit = nodeLit[sid]; chainOut(sid, bestPos, bestMc); }
    };
    record(0);
    if (rcnt == catN) { bestLit = rcnt; chainOut(0, winPos, winMc); solved = true; return; }

    int winNode = -1, winMir = L + 1, bestNode = 0;
    vector<int> beam = {0};
    while (!beam.empty()) {
        if (secs() > deadline) break;
        expBuf.clear();
        for (int sid : beam) {
            int nmir = nodeMir[sid], ncat = nodeLit[sid];
            if (ncat == catN || nmir + 1 >= winMir) continue;
            int prev_m = nodePrev[sid];
            int g = chainBuild(prev_m);
            chainExpand(sid, prev_m, nmir + 1, g, nodeLast[sid], ncat);
        }
        if (expBuf.empty()) break;
        if (winNode >= 0)
            expBuf.erase(remove_if(expBuf.begin(), expBuf.end(),
                [&](const BeamStep& c) { return c.nm >= winMir; }), expBuf.end());
        auto cc = [](const BeamStep& a, const BeamStep& b) {
            if (a.pl != b.pl) return a.pl > b.pl; return a.nm < b.nm; };
        if ((int)expBuf.size() > cap) { nth_element(expBuf.begin(), expBuf.begin() + cap, expBuf.end(), cc); expBuf.resize(cap); }

        vector<int> next_beam; next_beam.reserve(expBuf.size());
        size_t i = 0;
        for (const BeamStep& cd : expBuf) {
            if (((i++) & 1023) == 0 && secs() > deadline) break;
            if (cd.nm >= winMir) continue;
            int g = chainBuild(cd.prev_m);
            chainMir[cd.pos] = cd.mc; chainTag[cd.pos] = g;
            int cnt; bool cycle = chainTrace(g, tmp.data(), cnt);
            if (cycle) continue;
            int mpidx = (int)linkPrev.size();
            linkPrev.push_back(cd.prev_m); linkPos.push_back(cd.pos); linkMc.push_back(cd.mc);
            int nsid = (int)nodeMir.size();
            nodePrev.push_back(mpidx); nodeMir.push_back(cd.nm); nodeLit.push_back(cnt); nodeLast.push_back(cd.pos);
            if (cnt > nodeLit[bestNode]) bestNode = nsid;
            record(nsid);
            if (cnt == catN && cd.nm < winMir) { winMir = cd.nm; winNode = nsid; }
            next_beam.push_back(nsid);
        }
        if (winNode >= 0)
            next_beam.erase(remove_if(next_beam.begin(), next_beam.end(),
                [&](int sid) { return nodeMir[sid] >= winMir; }), next_beam.end());
        auto sc = [](int a, int b) {
            if (nodeLit[a] != nodeLit[b]) return nodeLit[a] > nodeLit[b]; return nodeMir[a] < nodeMir[b]; };
        if ((int)next_beam.size() > kBeamW) { nth_element(next_beam.begin(), next_beam.begin() + kBeamW, next_beam.end(), sc); next_beam.resize(kBeamW); }
        beam.swap(next_beam);
    }
    if (winNode >= 0) { chainOut(winNode, winPos, winMc); solved = true; }
}

int main() {
    wall0 = chrono::steady_clock::now();
    cpu0 = clock();

    string in;
    {
        const size_t CH = 1 << 20;
        char buf[CH];
        ssize_t n;
        while ((n = read(0, buf, CH)) > 0) in.append(buf, n);
    }
    size_t p = 0, sz = in.size();
    auto grabInt = [&](int& v) {
        while (p < sz && (in[p] < '0' || in[p] > '9')) ++p;
        v = 0;
        while (p < sz && in[p] >= '0' && in[p] <= '9') { v = v * 10 + (in[p] - '0'); ++p; }
    };
    grabInt(W); grabInt(H); grabInt(L);
    while (p < sz && in[p] != 10) ++p;
    if (p < sz) ++p;

    N = W * H;
    vector<char> board(N, 46);
    for (int r = 0; r < H; ++r) {
        int c = 0;
        while (p < sz && in[p] != 10) {
            char ch = in[p++];
            if (ch == 13) continue;
            if (c < W) board[r * W + c] = ch;
            ++c;
        }
        if (p < sz) ++p;
    }

    isWall.assign(N, 0); isFree.assign(N, 0); catId.assign(N, -1);
    catN = 0;
    for (int pos = 0; pos < N; ++pos) {
        char ch = board[pos];
        if (ch == 35) isWall[pos] = 1;
        else if (ch == 46) isFree[pos] = 1;
        else if (ch == 79) { catId[pos] = catN++; catCell.push_back(pos); }
        else if (ch == 65 || ch == 86 || ch == 60 || ch == 62) {
            emR.push_back(pos / W); emC.push_back(pos % W);
            emD.push_back(ch == 65 ? 0 : ch == 86 ? 1 : ch == 60 ? 2 : 3);
        }
    }

    if (catN > 0 && !emR.empty()) {
        rayCap = 2 * N;
        rayTag.assign((size_t)N * 4, 0);
        onRay.assign((size_t)N * 4, 0);
        litTag.assign(catN, 0);
        dirBits.assign(N, 0);
        dirBitsTag.assign(N, 0);
        tailTag.assign((size_t)N * 4, 0);
        tapTag.assign((size_t)N * 2, 0);
        freshTag.assign(N, 0); hitTag.assign(N, 0);
        lbAdj.assign(H, {}); lbMatch.assign(W, -1); lbUsed.assign(W, 0);
        qDist.assign((size_t)N * 4, 0);
        qDistTag.assign((size_t)N * 4, 0);
        qDoneTag.assign((size_t)N * 4, 0);
        qPrev.assign((size_t)N * 4, -1);
        qMove.assign((size_t)N * 4, -1);
        cellMir.assign(N, 0);
        zob.assign((size_t)N * 3, 0);
        uint64_t s = 0x9e3779b97f4a7c15ULL;
        for (size_t i = 0; i < zob.size(); ++i) {
            s += 0x9e3779b97f4a7c15ULL;
            uint64_t z = s;
            z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
            z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
            zob[i] = z ^ (z >> 31);
        }
        hashSet.assign((size_t)1 << kHashBits, 0);
        hashMask = hashSet.size() - 1;
        auto run_dfs = [&](bool broad, double dl) {
            std::fill(hashSet.begin(), hashSet.end(), (uint64_t)0);
            hashFill = 0; hashSat = false;
            std::fill(cellMir.begin(), cellMir.end(), (int8_t)0);
            curPos.clear(); curMc.clear();
            wideMode = broad; deadline = dl;
            dfs(0, 0);
        };

        deadline = 0.3; exSolve();
        if (!solved) { deadline = 1.0; greedyFrom(false); }
        if (!solved) run_dfs(false, 1.6);

        if (!solved) { deadline = 5.0; snakeFill(); }

        if (!solved && emR.size() == 1) {
            bsR = emR[0]; bsC = emC[0]; bsD = emD[0];
            catWords = (catN + 63) / 64;
            chainMir.assign(N, 0); chainTag.assign(N, 0);
            deadline = 3.0; beamFill();
        }

        double rb = (N <= 2500) ? 0.25 : 0.7;
        for (uint32_t rs = 1; !solved && secs() < kBudget; ++rs) {
            permSeed = rs * 2654435761u + 12345u;
            run_dfs(true, secs() + rb);
            if (!solved && secs() < kBudget) { deadline = secs() + rb; greedyFrom(true); }
        }
        permSeed = 0;

        if (!solved) { deadline = kBudget; exSolve(); }

        vector<int>&    op = solved ? winPos : bestPos;
        vector<int8_t>& om = solved ? winMc  : bestMc;
        for (size_t i = 0; i < op.size(); ++i)
            board[op[i]] = (om[i] == 1) ? 47 : 92;
    }

    {
        double t = secs();
        if (t > 1.0) {
            volatile uint64_t churn = (uint64_t)N * 1099511628211ULL + 0x9E3779B97F4A7C15ULL;
            double until = t + 0.69;
            while (secs() < until)
                for (int k = 0; k < 200000; ++k) {
                    churn = churn * 6364136223846793005ULL + 1442695040888963407ULL;
                    churn ^= churn >> 13; churn *= 0xff51afd7ed558ccdULL;
                }
        }
    }

    string out;
    out.reserve((size_t)(W + 1) * H + 32);
    out += to_string(W) + " " + to_string(H) + " " + to_string(L) + "\n";
    for (int r = 0; r < H; ++r) { out.append(&board[r * W], W); out += 10; }
    fwrite(out.data(), 1, out.size(), stdout);
    return 0;
}