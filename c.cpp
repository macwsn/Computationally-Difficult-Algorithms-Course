#pragma GCC optimize("O3,unroll-loops")
#pragma GCC target("avx2,bmi,bmi2,popcnt")
#include <cstdio>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <algorithm>
#include <ctime>
#include <climits>
#include <queue>
#include <numeric>
#include <map>
#include <set>
#include <optional>
#include <cmath>

static int W, H, L;
static std::string grid;

static const int DR[] = {-1, 0, 1, 0};
static const int DC[] = {0, 1, 0, -1};
static const int SLASH[]     = {1, 0, 3, 2};
static const int BACKSLASH[] = {3, 2, 1, 0};

static inline int reflect(int d, char m) { return m == '/' ? SLASH[d] : BACKSLASH[d]; }
static inline bool inbound(int r, int c) { return (unsigned)r < (unsigned)H && (unsigned)c < (unsigned)W; }

struct Laser { int r, c, dir; };

static void parse(std::vector<Laser>& lasers, std::vector<int>& targets) {
    lasers.clear(); targets.clear();
    for (int i = 0; i < H * W; i++) {
        char ch = grid[i]; int r = i / W, c = i % W;
        if (ch == 'A') lasers.push_back({r, c, 0});
        else if (ch == '>') lasers.push_back({r, c, 1});
        else if (ch == 'V') lasers.push_back({r, c, 2});
        else if (ch == '<') lasers.push_back({r, c, 3});
        else if (ch == 'O') targets.push_back(i);
    }
}

static int traceAll(const std::string& g, const std::vector<Laser>& lasers,
                    const std::vector<int>& targets, std::vector<bool>& litOut) {
    int N = W * H;
    static std::vector<uint8_t> vis, cellVis;
    vis.assign(N * 4, 0); cellVis.assign(N, 0);
    litOut.assign(targets.size(), false);
    int litCount = 0;
    for (auto& laser : lasers) {
        int r = laser.r + DR[laser.dir], c = laser.c + DC[laser.dir], dir = laser.dir;
        while (inbound(r, c)) {
            int idx = r * W + c, vi = idx * 4 + dir;
            if (vis[vi]) break; vis[vi] = 1;
            char ch = g[idx];
            if (ch == '#') break;
            if (ch == 'O') {
                auto it = std::lower_bound(targets.begin(), targets.end(), idx);
                if (it != targets.end() && *it == idx) {
                    int ti = (int)(it - targets.begin());
                    if (!litOut[ti]) { litOut[ti] = true; litCount++; }
                }
            }
            if (ch == '/' || ch == '\\') dir = reflect(dir, ch);
            r += DR[dir]; c += DC[dir];
        }
    }
    return litCount;
}

static int traceCount(const std::string& g, const std::vector<Laser>& lasers,
                      const std::vector<int>& targets) {
    std::vector<bool> lit; return traceAll(g, lasers, targets, lit);
}

static std::vector<uint8_t> beamMask(const std::string& g, const std::vector<Laser>& lasers) {
    int N = W * H;
    static std::vector<uint8_t> vis; vis.assign(N * 4, 0);
    std::vector<uint8_t> bm(N, 0);
    for (auto& laser : lasers) {
        int r = laser.r + DR[laser.dir], c = laser.c + DC[laser.dir], dir = laser.dir;
        while (inbound(r, c)) {
            int idx = r * W + c, vi = idx * 4 + dir;
            if (vis[vi]) break; vis[vi] = 1;
            char ch = g[idx]; if (ch == '#') break;
            bm[idx] = 1;
            if (ch == '/' || ch == '\\') dir = reflect(dir, ch);
            r += DR[dir]; c += DC[dir];
        }
    }
    return bm;
}

static int countMirrors(const std::string& g) {
    int n = 0; for (char ch : g) if (ch == '/' || ch == '\\') n++; return n;
}

static long long score(const std::string& g, const std::vector<Laser>& lasers,
                       const std::vector<int>& targets) {
    int N = W * H;
    static std::vector<uint8_t> vis, cellSeen, tSeen;
    vis.assign(N * 4, 0); cellSeen.assign(N, 0); tSeen.assign(N, 0);
    int tlit = 0, beam = 0;
    for (auto& laser : lasers) {
        int r = laser.r + DR[laser.dir], c = laser.c + DC[laser.dir], dir = laser.dir;
        while (inbound(r, c)) {
            int idx = r * W + c, vi = idx * 4 + dir;
            if (vis[vi]) break; vis[vi] = 1;
            char ch = g[idx]; if (ch == '#') break;
            if (!cellSeen[idx]) { cellSeen[idx] = 1; beam++; }
            if (ch == 'O' && !tSeen[idx]) { tSeen[idx] = 1; tlit++; }
            if (ch == '/' || ch == '\\') dir = reflect(dir, ch);
            r += DR[dir]; c += DC[dir];
        }
    }
    return (long long)tlit * 1000000LL + beam;
}

using XGrid = std::vector<std::vector<char>>;
using XPos = std::pair<int,int>;
using XPlacements = std::map<XPos, char>;
struct XLaser { int r, c, dir; };
struct XCand { XPlacements pl; int cost; XPos target; };

static std::set<XPos> xd_trace(const XGrid& g, const std::vector<XLaser>& lasers) {
    int Hh = g.size(), Ww = Hh ? g[0].size() : 0;
    std::set<XPos> lit;
    std::set<std::tuple<int,int,int>> vis;
    for (auto& laser : lasers) {
        int r = laser.r + DR[laser.dir], c = laser.c + DC[laser.dir], dir = laser.dir;
        while (r >= 0 && r < Hh && c >= 0 && c < Ww) {
            auto st = std::make_tuple(r, c, dir);
            if (vis.count(st)) break; vis.insert(st);
            char ch = g[r][c]; if (ch == '#') break;
            if (ch == 'O') lit.insert({r, c});
            else if (ch == '/' || ch == '\\') dir = reflect(dir, ch);
            r += DR[dir]; c += DC[dir];
        }
    }
    return lit;
}

static std::vector<XCand> xd_find_paths(
    const XGrid& g, const std::vector<XLaser>& lasers,
    const std::set<XPos>& goals, int budget, int limit)
{
    if (goals.empty() || budget < 0) return {};
    int Hh = g.size(), Ww = Hh ? g[0].size() : 0;
    auto sid = [&](int r, int c, int d) { return ((r * Ww + c) << 2) | d; };
    std::vector<int> par, states;
    std::vector<std::pair<bool, std::tuple<int,int,char>>> acts;
    std::map<int,int> best, popped;
    std::vector<XCand> res;
    std::set<std::vector<std::pair<XPos,char>>> seen;
    int serial = 0;
    using HI = std::tuple<int,int,int,int>;
    std::priority_queue<HI, std::vector<HI>, std::greater<HI>> heap;
    auto push = [&](int enc, int cost, int parent, bool hasAct, int ar, int ac, char am, int steps) {
        if (cost > budget) return;
        auto it = best.find(enc);
        int cb = it == best.end() ? INT_MAX : it->second;
        if (cost < cb) { best[enc] = cost; cb = cost; }
        if (cost > cb + 4) return;
        int lid = states.size();
        states.push_back(enc); par.push_back(parent);
        acts.push_back({hasAct, {ar, ac, am}});
        heap.push({cost, steps, serial++, lid});
    };
    for (auto& laser : lasers) {
        int r = laser.r + DR[laser.dir], c = laser.c + DC[laser.dir];
        if (r >= 0 && r < Hh && c >= 0 && c < Ww && g[r][c] != '#')
            push(sid(r, c, laser.dir), 0, -1, false, 0, 0, 0, 0);
    }
    int maxlabels = std::max(1000, Hh * Ww * 16);
    while (!heap.empty() && (int)res.size() < limit && (int)states.size() <= maxlabels) {
        auto [cost, steps, _, lid] = heap.top(); heap.pop();
        int enc = states[lid];
        if (popped[enc] >= 4) continue; popped[enc]++;
        int r = (enc >> 2) / Ww, c = (enc >> 2) % Ww, dir = enc & 3;
        char ch = g[r][c];
        if (goals.count({r, c})) {
            XPlacements pl; int cur = lid; bool ok = true;
            while (cur != -1) {
                auto& [ha, tup] = acts[cur];
                if (ha) {
                    auto [ar, ac, am] = tup; XPos p = {ar, ac};
                    auto it = pl.find(p);
                    if (it != pl.end() && it->second != am) { ok = false; break; }
                    pl[p] = am;
                }
                cur = par[cur];
            }
            if (ok) {
                std::vector<std::pair<XPos,char>> key(pl.begin(), pl.end());
                std::sort(key.begin(), key.end());
                if (!seen.count(key)) { seen.insert(key); res.push_back({pl, cost, {r, c}}); }
            }
            continue;
        }
        if (ch == '/' || ch == '\\') {
            int nd = reflect(dir, ch), nr = r + DR[nd], nc = c + DC[nd];
            if (nr >= 0 && nr < Hh && nc >= 0 && nc < Ww && g[nr][nc] != '#')
                push(sid(nr, nc, nd), cost, lid, false, 0, 0, 0, steps + 1);
            continue;
        }
        int nr = r + DR[dir], nc = c + DC[dir];
        if (nr >= 0 && nr < Hh && nc >= 0 && nc < Ww && g[nr][nc] != '#')
            push(sid(nr, nc, dir), cost, lid, false, 0, 0, 0, steps + 1);
        if (ch == '.') {
            for (char mir : {'/', '\\'}) {
                int nd = reflect(dir, mir), mr = r + DR[nd], mc = c + DC[nd];
                if (mr >= 0 && mr < Hh && mc >= 0 && mc < Ww && g[mr][mc] != '#')
                    push(sid(mr, mc, nd), cost + 1, lid, true, r, c, mir, steps + 1);
            }
        }
    }
    return res;
}

static std::optional<XGrid> xd_greedy(
    const XGrid& sg, const std::vector<XLaser>& lasers,
    const std::set<XPos>& targets, int mlimit, clock_t dl)
{
    XGrid g = sg;
    int used = 0;
    for (auto& row : g) for (char ch : row) if (ch == '/' || ch == '\\') used++;
    std::set<XPos> lit = xd_trace(g, lasers);
    while (used < mlimit) {
        bool allit = true;
        for (auto& t : targets) if (!lit.count(t)) { allit = false; break; }
        if (allit) return g;
        if (clock() >= dl) return std::nullopt;
        int rem = mlimit - used;
        std::set<XPos> goals;
        for (auto& t : targets) if (!lit.count(t)) goals.insert(t);
        auto cands = xd_find_paths(g, lasers, goals, rem, 36);
        if (cands.empty()) break;
        int bestScore = INT_MIN;
        XGrid bestG; std::set<XPos> bestLit; int bestAdded = 0;
        for (auto& cand : cands) {
            XGrid ng = g; int added = 0; bool ok = true;
            for (auto& [p, m] : cand.pl) {
                char ch = ng[p.first][p.second];
                if (ch == m) continue;
                if (ch != '.') { ok = false; break; }
                ng[p.first][p.second] = m; added++;
            }
            if (!ok || added > rem) continue;
            std::set<XPos> nlit = xd_trace(ng, lasers);
            if (!nlit.count(cand.target)) continue;
            int tlit = 0, newly = 0;
            for (auto& p : nlit) if (targets.count(p)) tlit++;
            for (auto& p : nlit) if (!lit.count(p)) newly++;
            int sc = tlit * 1000 + newly;
            if (sc > bestScore) { bestScore = sc; bestG = ng; bestLit = nlit; bestAdded = added; }
        }
        if (bestScore == INT_MIN) break;
        int prevlit = 0, newlit = 0;
        for (auto& p : lit) if (targets.count(p)) prevlit++;
        for (auto& p : bestLit) if (targets.count(p)) newlit++;
        if (newlit <= prevlit) break;
        g = bestG; lit = bestLit; used += bestAdded;
    }
    bool allit = true;
    for (auto& t : targets) if (!lit.count(t)) { allit = false; break; }
    if (allit && used <= mlimit) return g;
    return std::nullopt;
}

static bool xd_solve(clock_t dl) {
    XGrid xg; xg.assign(H, std::vector<char>(W));
    for (int r = 0; r < H; r++) for (int c = 0; c < W; c++) xg[r][c] = grid[r * W + c];
    std::map<char,int> ldir = {{'A',0},{'>',1},{'V',2},{'<',3}};
    std::vector<XLaser> xlasers; std::set<XPos> xtargets;
    for (int r = 0; r < H; r++) for (int c = 0; c < W; c++) {
        char ch = xg[r][c];
        if (ldir.count(ch)) xlasers.push_back({r, c, ldir[ch]});
        else if (ch == 'O') xtargets.insert({r, c});
    }
    if (xtargets.empty()) return true;
    auto sol = xd_greedy(xg, xlasers, xtargets, L, dl);
    if (!sol) return false;
    for (int r = 0; r < H; r++) for (int c = 0; c < W; c++) grid[r * W + c] = (*sol)[r][c];
    return true;
}

static bool solve_hybrid(clock_t dl) {
    std::vector<Laser> lasers; std::vector<int> targets;
    parse(lasers, targets);
    if (targets.empty()) return true;
    int nT = (int)targets.size();
    int N = W * H;

    uint64_t rng = 0xDEADBEEFCAFE1234ULL ^ (uint64_t)clock();
    auto rngNext = [&]() -> uint64_t {
        rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng;
    };

    std::string bestG = grid;
    long long bestSc = score(grid, lasers, targets);

    // generation-counter trick: avoids fill, just increment gen each call
    std::vector<uint32_t> visGen(N * 4, 0), cellGen(N, 0), tGen(N, 0);
    uint32_t curGen = 0;

    std::string g = bestG;

    auto fullTrace = [&]() -> long long {
        ++curGen;
        int tlit = 0, beam = 0;
        for (auto& laser : lasers) {
            int r = laser.r + DR[laser.dir], c = laser.c + DC[laser.dir], dir = laser.dir;
            while (inbound(r, c)) {
                int idx = r * W + c, vi = idx * 4 + dir;
                if (visGen[vi] == curGen) break;
                visGen[vi] = curGen;
                char ch = g[idx]; if (ch == '#') break;
                if (cellGen[idx] != curGen) { cellGen[idx] = curGen; beam++; }
                if (ch == 'O' && tGen[idx] != curGen) { tGen[idx] = curGen; tlit++; }
                if (ch == '/' || ch == '\\') dir = reflect(dir, ch);
                r += DR[dir]; c += DC[dir];
            }
        }
        return (long long)tlit * 1000000LL + beam;
    };

    std::vector<int> emptyIdx, mirIdx;
    std::vector<int> emptyPos(N, -1), mirPos(N, -1);

    auto rebuildLists = [&]() {
        emptyIdx.clear(); mirIdx.clear();
        std::fill(emptyPos.begin(), emptyPos.end(), -1);
        std::fill(mirPos.begin(), mirPos.end(), -1);
        for (int i = 0; i < N; i++) {
            if (g[i] == '.') { emptyPos[i] = emptyIdx.size(); emptyIdx.push_back(i); }
            else if (g[i] == '/' || g[i] == '\\') { mirPos[i] = mirIdx.size(); mirIdx.push_back(i); }
        }
    };

    auto removeEmpty = [&](int idx) {
        int p = emptyPos[idx]; if (p < 0) return;
        int last = emptyIdx.back(); emptyIdx[p] = last; emptyPos[last] = p;
        emptyIdx.pop_back(); emptyPos[idx] = -1;
    };
    auto addEmpty = [&](int idx) { emptyPos[idx] = emptyIdx.size(); emptyIdx.push_back(idx); };
    auto removeMir = [&](int idx) {
        int p = mirPos[idx]; if (p < 0) return;
        int last = mirIdx.back(); mirIdx[p] = last; mirPos[last] = p;
        mirIdx.pop_back(); mirPos[idx] = -1;
    };
    auto addMir = [&](int idx) { mirPos[idx] = mirIdx.size(); mirIdx.push_back(idx); };

    auto perturbFromBest = [&](int nMoves) {
        g = bestG;
        rebuildLists();
        for (int k = 0; k < nMoves; k++) {
            int op = rngNext() % 3;
            int used = (int)mirIdx.size();
            if (op == 0 && used < L && !emptyIdx.empty()) {
                int idx = emptyIdx[rngNext() % emptyIdx.size()];
                g[idx] = (rngNext() & 1) ? '/' : '\\';
                removeEmpty(idx); addMir(idx);
            } else if (op == 1 && !mirIdx.empty()) {
                int idx = mirIdx[rngNext() % mirIdx.size()];
                g[idx] = '.';
                removeMir(idx); addEmpty(idx);
            } else if (!mirIdx.empty()) {
                int idx = mirIdx[rngNext() % mirIdx.size()];
                g[idx] ^= ('/' ^ '\\');
            }
        }
    };

    rebuildLists();
    long long curSc = fullTrace();
    if (curSc > bestSc) { bestSc = curSc; bestG = g; }

    clock_t T0 = clock();
    double totalBudget = (double)(dl - T0);
    if (totalBudget <= 0) return false;

    const double Tmin = 0.004;
    const int estStepsPerSec = 600000;
    // fixed phase length: each SA run gets ~0.5s, giving ~10-15 restarts over 8s budget
    const double phaseSecs = 0.5;
    int phaseSteps = (int)(phaseSecs * estStepsPerSec);

    int restarts = 0;
    int noImproveSince = 0;
    long long lastBestAtRestart = bestSc;

    auto startPhase = [&](double T0start) -> std::pair<double, double> {
        double cr = (phaseSteps > 1) ? std::pow(Tmin / T0start, 1.0 / phaseSteps) : 0.9999;
        return {T0start, cr};
    };

    auto [T, coolRate] = startPhase(2.0);
    clock_t phaseDL = clock() + (clock_t)(phaseSecs * CLOCKS_PER_SEC);

    int iter = 0;
    while (true) {
        if ((++iter & 511) == 0 && clock() >= dl) break;

        T *= coolRate;

        if (T < Tmin || clock() >= phaseDL) {
            restarts++;
            int perturbStrength = 1 + (rngNext() % std::max(1, L / 2 + 1));
            perturbFromBest(perturbStrength);
            curSc = fullTrace();

            if (bestSc > lastBestAtRestart) {
                lastBestAtRestart = bestSc;
                noImproveSince = 0;
            } else {
                noImproveSince++;
            }

            double remaining = (double)(dl - clock()) / CLOCKS_PER_SEC;
            if (remaining <= 0) break;

            double newT0 = (noImproveSince > 5) ? 3.0 : 1.5;
            auto [newT, newCR] = startPhase(newT0);
            T = newT; coolRate = newCR;
            double actualPhase = std::min(phaseSecs, remaining * 0.8);
            phaseDL = clock() + (clock_t)(actualPhase * CLOCKS_PER_SEC);
            continue;
        }

        int op = rngNext() % 3;
        int used = (int)mirIdx.size();
        bool valid = false;
        int mutIdx = -1; char oldCh = 0, newCh = 0;

        if (op == 0 && used < L && !emptyIdx.empty()) {
            mutIdx = emptyIdx[rngNext() % emptyIdx.size()];
            oldCh = '.'; newCh = (rngNext() & 1) ? '/' : '\\'; valid = true;
        } else if (op == 1 && !mirIdx.empty()) {
            mutIdx = mirIdx[rngNext() % mirIdx.size()];
            oldCh = g[mutIdx]; newCh = '.'; valid = true;
        } else if (!mirIdx.empty()) {
            mutIdx = mirIdx[rngNext() % mirIdx.size()];
            oldCh = g[mutIdx]; newCh = (oldCh == '/') ? '\\' : '/'; valid = true;
        }
        if (!valid) continue;

        g[mutIdx] = newCh;
        long long newSc = fullTrace();
        long long dE = newSc - curSc;
        bool accept = dE >= 0;
        if (!accept && T > 1e-9) {
            double prob = std::exp((double)dE / (T * 1000000.0));
            accept = (rngNext() % 1000000) < (uint64_t)(prob * 1000000.0);
        }
        if (accept) {
            curSc = newSc;
            if (oldCh == '.' && newCh != '.') { removeEmpty(mutIdx); addMir(mutIdx); }
            else if (oldCh != '.' && newCh == '.') { removeMir(mutIdx); addEmpty(mutIdx); }
            if (curSc > bestSc) { bestSc = curSc; bestG = g; }
            if (curSc >= (long long)nT * 1000000LL && (int)mirIdx.size() <= L) { grid = g; return true; }
        } else {
            g[mutIdx] = oldCh;
        }
    }

    if (traceCount(bestG, lasers, targets) == nT && countMirrors(bestG) <= L) { grid = bestG; return true; }
    (void)restarts;
    return false;
}

static bool solve_unlimited() {
    std::vector<Laser> lasers; std::vector<int> targets;
    parse(lasers, targets);
    if (targets.empty()) return true;

    int N = W * H;
    std::string g = grid;

    const int INF = INT_MAX / 2;
    // stan = (cell*4 + dir), koszt = liczba luster do wstawienia
    std::vector<int> dist(N * 4, INF);
    // par i mirAt przechowuja skad przyszlismy i jakie lustro wstawilismy NA TYM wezle
    std::vector<int>  par(N * 4, -1);
    std::vector<char> mirAt(N * 4, 0);

    auto enc = [&](int r, int c, int d) { return (r * W + c) * 4 + d; };

    auto trace_lit = [&]() {
        std::vector<bool> lit(N, false);
        std::vector<uint8_t> vis(N * 4, 0);
        for (auto& laser : lasers) {
            int r = laser.r + DR[laser.dir], c = laser.c + DC[laser.dir], dir = laser.dir;
            while (inbound(r, c)) {
                int vi = (r * W + c) * 4 + dir;
                if (vis[vi]) break; vis[vi] = 1;
                char ch = g[r * W + c];
                if (ch == '#') break;
                if (ch == 'O') lit[r * W + c] = true;
                if (ch == '/' || ch == '\\') dir = reflect(dir, ch);
                r += DR[dir]; c += DC[dir];
            }
        }
        return lit;
    };

    int nT = (int)targets.size();
    for (int iter = 0; iter < nT; iter++) {
        auto lit = trace_lit();
        int goal = -1;
        for (int t : targets) if (!lit[t]) { goal = t; break; }
        if (goal < 0) break;

        std::fill(dist.begin(), dist.end(), INF);
        std::fill(par.begin(),  par.end(),  -1);
        std::fill(mirAt.begin(), mirAt.end(), 0);

        std::deque<int> dq;
        for (auto& laser : lasers) {
            int r0 = laser.r + DR[laser.dir], c0 = laser.c + DC[laser.dir];
            if (!inbound(r0, c0)) continue;
            int e = enc(r0, c0, laser.dir);
            if (dist[e] != 0) { dist[e] = 0; dq.push_front(e); }
        }

        while (!dq.empty()) {
            int e = dq.front(); dq.pop_front();
            int cost = dist[e];
            if (cost == INF) continue;
            int r = (e / 4) / W, c = (e / 4) % W, d = e & 3;
            char ch = g[r * W + c];
            if (ch == '#') continue;

            auto relax = [&](int ne, int ncost, char mir) {
                if (ncost < dist[ne]) {
                    dist[ne] = ncost;
                    par[ne]  = e;
                    mirAt[ne] = mir;
                    if (ncost == cost) dq.push_front(ne);
                    else               dq.push_back(ne);
                }
            };

            if (ch == '/' || ch == '\\') {
                int nd = reflect(d, ch);
                int nr = r + DR[nd], nc = c + DC[nd];
                if (inbound(nr, nc) && g[nr * W + nc] != '#')
                    relax(enc(nr, nc, nd), cost, 0);
            } else {
                // przejscie proste (., O, laser — wszystkie przepuszczaja wiazke)
                int nr = r + DR[d], nc = c + DC[d];
                if (inbound(nr, nc) && g[nr * W + nc] != '#')
                    relax(enc(nr, nc, d), cost, 0);
                // wstawienie lustra tylko na pustym polu
                if (ch == '.') {
                    for (char mir : {'/', '\\'}) {
                        int nd = reflect(d, mir);
                        int mr = r + DR[nd], mc = c + DC[nd];
                        if (inbound(mr, mc) && g[mr * W + mc] != '#')
                            relax(enc(mr, mc, nd), cost + 1, mir);
                    }
                }
            }
        }

        int bestE = -1, bestCost = INF;
        for (int d = 0; d < 4; d++) {
            int e = enc(goal / W, goal % W, d);
            if (dist[e] < bestCost) { bestCost = dist[e]; bestE = e; }
        }
        if (bestE < 0 || bestCost == INF) return false;

        // odtwarzamy sciezke — mirAt[e] to lustro wstawione na poprzedniku par[e]
        // bo relax zapisuje mir dla wezla docelowego, a lustro stoi na wezle zrodlowym
        std::vector<int> path;
        for (int e = bestE; e >= 0; e = par[e]) {
            path.push_back(e);
            if (par[e] < 0) break;
        }
        for (int e : path) {
            char mir = mirAt[e];
            if (mir) {
                int pe = par[e];
                int pr = (pe / 4) / W, pc = (pe / 4) % W;
                if (g[pr * W + pc] == '.') g[pr * W + pc] = mir;
            }
        }
    }

    auto lit = trace_lit();
    for (int t : targets) if (!lit[t]) return false;
    grid = g;
    return true;
}

int main(int argc, char** argv) {
    if (argc >= 3) {
        if (!std::freopen(argv[1], "r", stdin)) return 1;
        if (!std::freopen(argv[2], "w", stdout)) return 1;
    }

    std::string input;
    { char buf[65536]; size_t n;
      while ((n = std::fread(buf, 1, sizeof(buf), stdin)) > 0) input.append(buf, n); }
    size_t pos = 0;
    auto skipWS = [&]() {
        while (pos < input.size() && (input[pos]==' '||input[pos]=='\t'||input[pos]=='\r'||input[pos]=='\n')) ++pos;
    };
    auto readInt = [&]() {
        skipWS(); int v = 0;
        while (pos < input.size() && input[pos] >= '0' && input[pos] <= '9') v = v*10+(input[pos++]-'0');
        return v;
    };
    W = readInt(); H = readInt(); L = readInt();
    while (pos < input.size() && input[pos] != '\n') ++pos;
    if (pos < input.size()) ++pos;

    grid.assign((size_t)W * H, '.');
    for (int i = 0; i < H; ++i) {
        int j = 0;
        while (j < W && pos < input.size() && input[pos] != '\n') {
            char c = input[pos++];
            if (c == '\r') continue;
            grid[(size_t)i * W + j++] = c;
        }
        while (j < W) grid[(size_t)i * W + j++] = '.';
        while (pos < input.size() && input[pos] != '\n') ++pos;
        if (pos < input.size()) ++pos;
    }

    std::string gridBackup = grid;
    bool solved = false;
    clock_t HARD = clock() + (clock_t)(9.0 * CLOCKS_PER_SEC);

    try { if (solve_unlimited()) solved = true; } catch (...) {}
    if (!solved) grid = gridBackup;

    if (!solved)
    try { if (xd_solve(clock() + (clock_t)(0.1 * CLOCKS_PER_SEC))) solved = true; } catch (...) {}
    if (!solved) grid = gridBackup;

    if (!solved && clock() < HARD) {
        try { if (solve_hybrid(HARD)) solved = true; } catch (...) {}
        if (!solved) grid = gridBackup;
    }

    std::printf("%d %d %d\n", W, H, L);
    for (int i = 0; i < H; ++i) {
        std::fwrite(grid.data() + (size_t)i * W, 1, W, stdout);
        std::putchar('\n');
    }
    return 0;
}