#pragma GCC optimize("O3,unroll-loops,inline")
#pragma GCC target("avx2,bmi,bmi2,popcnt")
#include <cstdio>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <algorithm>
#include <ctime>
#include <map>
#include <set>
#include <tuple>
#include <optional>
#include <climits>
#include <queue>
#include <deque>
#include <chrono>
#include <random>
#include <unordered_set>

static int W, H, L;
static std::string grid;

const int XD_DR[] = {-1, 0, 1, 0};
const int XD_DC[] = {0, 1, 0, -1};
const int XD_SLASH[] = {1, 0, 3, 2};
const int XD_BACKSLASH[] = {3, 2, 1, 0};

static int xd_reflect(int d, char m) {
    return m == '/' ? XD_SLASH[d] : XD_BACKSLASH[d];
}

using XGrid = std::vector<std::vector<char>>;
using XPos = std::pair<int,int>;
using XPlacements = std::map<XPos, char>;

struct XLaser { int r, c, dir; };

/*
 xd_trace sledzi promien lasera po siatce i zwraca zbior pol ktore sa oswietlone.
 Odwiedza kazdy stan (row, col, kierunek) co najwyzej raz zeby nie wpasc w petle.
*/
static std::set<XPos> xd_trace(const XGrid& g, const std::vector<XLaser>& lasers) {
    int H = g.size();
    int W = H ? g[0].size() : 0;
    std::set<XPos> lit;
    std::set<std::tuple<int,int,int>> vis;
    for (auto& laser : lasers) {
        int r = laser.r + XD_DR[laser.dir];
        int c = laser.c + XD_DC[laser.dir];
        int dir = laser.dir;
        while (r >= 0 && r < H && c >= 0 && c < W) {
            auto st = std::make_tuple(r, c, dir);
            if (vis.count(st)) break;
            vis.insert(st);
            char ch = g[r][c];
            if (ch == '#') break;
            if (ch == 'O') lit.insert({r, c});
            else if (ch == '/' || ch == '\\') dir = xd_reflect(dir, ch);
            r += XD_DR[dir];
            c += XD_DC[dir];
        }
    }
    return lit;
}

struct XCand { XPlacements pl; int cost; XPos target; };

/*
 xd_find_paths szuka sciezek od lasera do kazdego celu uzywajac kolejki priorytetowej.
 Pozwala na tolerancje +4 kosztu zeby znalezc rozne ukladki luster.
*/
static std::vector<XCand> xd_find_paths(
    const XGrid& g,
    const std::vector<XLaser>& lasers,
    const std::set<XPos>& goals,
    int budget,
    int limit)
{
    if (goals.empty() || budget < 0) return {};
    int H = g.size();
    int W = H ? g[0].size() : 0;
    auto sid = [&](int r, int c, int d) { return ((r * W + c) << 2) | d; };

    std::vector<int> par;
    std::vector<int> states;
    std::vector<std::pair<bool, std::tuple<int,int,char>>> acts;
    std::map<int,int> best;
    std::map<int,int> popped;
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
        states.push_back(enc);
        par.push_back(parent);
        acts.push_back({hasAct, {ar, ac, am}});
        heap.push({cost, steps, serial++, lid});
    };

    for (auto& laser : lasers) {
        int r = laser.r + XD_DR[laser.dir];
        int c = laser.c + XD_DC[laser.dir];
        if (r >= 0 && r < H && c >= 0 && c < W && g[r][c] != '#')
            push(sid(r, c, laser.dir), 0, -1, false, 0, 0, 0, 0);
    }

    int maxlabels = std::max(1000, H * W * 4 * 4);
    while (!heap.empty() && (int)res.size() < limit && (int)states.size() <= maxlabels) {
        auto [cost, steps, _, lid] = heap.top();
        heap.pop();
        int enc = states[lid];
        if (popped[enc] >= 4) continue;
        popped[enc]++;
        int r = (enc >> 2) / W;
        int c = (enc >> 2) % W;
        int dir = enc & 3;
        char ch = g[r][c];
        if (goals.count({r, c})) {
            XPlacements pl;
            int cur = lid;
            bool ok = true;
            while (cur != -1) {
                auto& [ha, tup] = acts[cur];
                if (ha) {
                    auto [ar, ac, am] = tup;
                    XPos p = {ar, ac};
                    auto it = pl.find(p);
                    if (it != pl.end() && it->second != am) { ok = false; break; }
                    pl[p] = am;
                }
                cur = par[cur];
            }
            if (ok) {
                std::vector<std::pair<XPos,char>> key(pl.begin(), pl.end());
                std::sort(key.begin(), key.end());
                if (!seen.count(key)) {
                    seen.insert(key);
                    res.push_back({pl, cost, {r, c}});
                }
            }
            continue;
        }
        if (ch == '/' || ch == '\\') {
            int nd = xd_reflect(dir, ch);
            int nr = r + XD_DR[nd];
            int nc = c + XD_DC[nd];
            if (nr >= 0 && nr < H && nc >= 0 && nc < W && g[nr][nc] != '#')
                push(sid(nr, nc, nd), cost, lid, false, 0, 0, 0, steps + 1);
            continue;
        }
        int nr = r + XD_DR[dir];
        int nc = c + XD_DC[dir];
        if (nr >= 0 && nr < H && nc >= 0 && nc < W && g[nr][nc] != '#')
            push(sid(nr, nc, dir), cost, lid, false, 0, 0, 0, steps + 1);
        if (ch == '.') {
            for (char mir : {'/', '\\'}) {
                int nd = xd_reflect(dir, mir);
                int mr = r + XD_DR[nd];
                int mc = c + XD_DC[nd];
                if (mr >= 0 && mr < H && mc >= 0 && mc < W && g[mr][mc] != '#')
                    push(sid(mr, mc, nd), cost + 1, lid, true, r, c, mir, steps + 1);
            }
        }
    }
    return res;
}

/*
 xd_greedy zachlannie wybiera najlepszego kandydata z xd_find_paths i uklada lustro.
 Powtarza az oswietli wszystkie cele lub zabraknie luster.
*/
static std::optional<XGrid> xd_greedy(
    const XGrid& sg,
    const std::vector<XLaser>& lasers,
    const std::set<XPos>& targets,
    int mlimit,
    clock_t dl)
{
    XGrid g = sg;
    int used = 0;
    for (auto& row : g)
        for (char ch : row)
            if (ch == '/' || ch == '\\') used++;
    std::set<XPos> lit = xd_trace(g, lasers);
    while (used < mlimit) {
        bool allit = true;
        for (auto& t : targets)
            if (!lit.count(t)) { allit = false; break; }
        if (allit) return g;
        if (clock() >= dl) return std::nullopt;
        int rem = mlimit - used;
        std::set<XPos> goals;
        for (auto& t : targets)
            if (!lit.count(t)) goals.insert(t);
        auto cands = xd_find_paths(g, lasers, goals, rem, 36);
        if (cands.empty()) break;
        int bestScore = INT_MIN;
        XGrid bestG;
        std::set<XPos> bestLit;
        int bestAdded = 0;
        for (auto& cand : cands) {
            XGrid ng = g;
            int added = 0;
            bool ok = true;
            for (auto& [p, m] : cand.pl) {
                char ch = ng[p.first][p.second];
                if (ch == m) continue;
                if (ch != '.') { ok = false; break; }
                ng[p.first][p.second] = m;
                added++;
            }
            if (!ok || added > rem) continue;
            std::set<XPos> nlit = xd_trace(ng, lasers);
            if (!nlit.count(cand.target)) continue;
            int tlit = 0;
            int newly = 0;
            for (auto& p : nlit) if (targets.count(p)) tlit++;
            for (auto& p : nlit) if (!lit.count(p)) newly++;
            int score = tlit * 1000 + newly;
            if (score > bestScore) { bestScore = score; bestG = ng; bestLit = nlit; bestAdded = added; }
        }
        if (bestScore == INT_MIN) break;
        int prevlit = 0;
        int newlit = 0;
        for (auto& p : lit) if (targets.count(p)) prevlit++;
        for (auto& p : bestLit) if (targets.count(p)) newlit++;
        if (newlit <= prevlit) break;
        g = bestG;
        lit = bestLit;
        used += bestAdded;
    }
    bool allit = true;
    for (auto& t : targets)
        if (!lit.count(t)) { allit = false; break; }
    if (allit && used <= mlimit) return g;
    return std::nullopt;
}

static void xd_parse(XGrid& g, std::vector<XLaser>& lasers, std::set<XPos>& targets) {
    g.assign(H, std::vector<char>(W));
    for (int r = 0; r < H; r++)
        for (int c = 0; c < W; c++)
            g[r][c] = grid[r * W + c];
    std::map<char,int> ldir = {{'A',0}, {'>',1}, {'V',2}, {'<',3}};
    for (int r = 0; r < H; r++) {
        for (int c = 0; c < W; c++) {
            char ch = g[r][c];
            if (ldir.count(ch)) lasers.push_back({r, c, ldir[ch]});
            else if (ch == 'O') targets.insert({r, c});
        }
    }
}

static void xd_commit(const XGrid& g) {
    for (int r = 0; r < H; r++)
        for (int c = 0; c < W; c++)
            grid[r * W + c] = g[r][c];
}

/*
 xd_solve to glowny solver zachlanny oparty na szukaniu sciezek do kolejnych celow.
 Wywoluje xd_greedy i zapisuje wynik do globalnej siatki jesli sie udalo.
*/
static bool xd_solve(clock_t dl) {
    XGrid g;
    std::vector<XLaser> lasers;
    std::set<XPos> targets;
    xd_parse(g, lasers, targets);
    if (targets.empty()) return true;
    auto sol = xd_greedy(g, lasers, targets, L, dl);
    if (!sol) return false;
    xd_commit(*sol);
    return true;
}

/*
 xd_random_solve losowo przesuwa kolejnosc kandydatow przy wyborze nastepnego lustra.
 Daje rozne rozwiazania przy powracaniu do petli.
*/
static bool xd_random_solve(clock_t dl) {
    XGrid g;
    std::vector<XLaser> lasers;
    std::set<XPos> targets;
    xd_parse(g, lasers, targets);
    if (targets.empty()) return true;

    uint64_t rng = 0xDEADBEEF12345678ULL ^ (uint64_t)clock();
    auto rng_next = [&]() -> uint64_t {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        return rng;
    };

    while (clock() < dl) {
        XGrid cur = g;
        int used = 0;
        for (auto& row : cur)
            for (char ch : row)
                if (ch == '/' || ch == '\\') used++;
        std::set<XPos> lit = xd_trace(cur, lasers);
        bool stuck = false;
        while (used < L && !stuck) {
            bool allit = true;
            for (auto& t : targets)
                if (!lit.count(t)) { allit = false; break; }
            if (allit) { xd_commit(cur); return true; }
            if (clock() >= dl) return false;
            int rem = L - used;
            std::set<XPos> goals;
            for (auto& t : targets)
                if (!lit.count(t)) goals.insert(t);
            auto cands = xd_find_paths(cur, lasers, goals, rem, 36);
            if (cands.empty()) { stuck = true; break; }
            for (int i = (int)cands.size() - 1; i > 0; i--) {
                int j = rng_next() % (i + 1);
                std::swap(cands[i], cands[j]);
            }
            int bestScore = INT_MIN;
            XGrid bestG;
            std::set<XPos> bestLit;
            int bestAdded = 0;
            int tryN = std::min((int)cands.size(), 6);
            for (int ci = 0; ci < tryN; ci++) {
                auto& cand = cands[ci];
                XGrid ng = cur;
                int added = 0;
                bool ok = true;
                for (auto& [p, m] : cand.pl) {
                    char ch = ng[p.first][p.second];
                    if (ch == m) continue;
                    if (ch != '.') { ok = false; break; }
                    ng[p.first][p.second] = m;
                    added++;
                }
                if (!ok || added > rem) continue;
                std::set<XPos> nlit = xd_trace(ng, lasers);
                if (!nlit.count(cand.target)) continue;
                int tlit = 0;
                int newly = 0;
                for (auto& p : nlit) if (targets.count(p)) tlit++;
                for (auto& p : nlit) if (!lit.count(p)) newly++;
                int score = tlit * 1000 + newly;
                if (score > bestScore) { bestScore = score; bestG = ng; bestLit = nlit; bestAdded = added; }
            }
            if (bestScore == INT_MIN) { stuck = true; break; }
            int prevlit = 0;
            int newlit = 0;
            for (auto& p : lit) if (targets.count(p)) prevlit++;
            for (auto& p : bestLit) if (targets.count(p)) newlit++;
            if (newlit <= prevlit) { stuck = true; break; }
            cur = bestG;
            lit = bestLit;
            used += bestAdded;
        }
        if (!stuck) {
            bool allit = true;
            for (auto& t : targets)
                if (!lit.count(t)) { allit = false; break; }
            if (allit && used <= L) { xd_commit(cur); return true; }
        }
    }
    return false;
}

/*
 xd_reverse_solve idzie od kazdego celu wstecz po siatce i szuka punktu przeciecia z promieniem.
 Umieszcza lustro w miejscu przeciecia zeby skierowac promien do celu.
*/
static bool xd_reverse_solve(clock_t dl) {
    XGrid g;
    std::vector<XLaser> lasers;
    std::set<XPos> targets;
    xd_parse(g, lasers, targets);
    if (targets.empty()) return true;

    int Hh = H;
    int Ww = W;
    auto fwd_cells = [&](const XGrid& gg) {
        std::set<std::pair<int,int>> cells;
        std::set<std::tuple<int,int,int>> vis;
        for (auto& laser : lasers) {
            int r = laser.r + XD_DR[laser.dir];
            int c = laser.c + XD_DC[laser.dir];
            int dir = laser.dir;
            while (r >= 0 && r < Hh && c >= 0 && c < Ww) {
                auto st = std::make_tuple(r, c, dir);
                if (vis.count(st)) break;
                vis.insert(st);
                char ch = gg[r][c];
                if (ch == '#') break;
                cells.insert({r, c});
                if (ch == '/' || ch == '\\') dir = xd_reflect(dir, ch);
                r += XD_DR[dir];
                c += XD_DC[dir];
            }
        }
        return cells;
    };

    const int OPP[] = {2, 3, 0, 1};
    XGrid cur = g;
    int used = 0;
    for (auto& row : cur)
        for (char ch : row)
            if (ch == '/' || ch == '\\') used++;
    std::set<XPos> lit = xd_trace(cur, lasers);
    int maxIter = L * 2;
    for (int iter = 0; iter < maxIter && used < L; iter++) {
        bool allit = true;
        for (auto& t : targets)
            if (!lit.count(t)) { allit = false; break; }
        if (allit) { xd_commit(cur); return true; }
        if (clock() >= dl) return false;
        auto fwd = fwd_cells(cur);
        std::set<XPos> goals;
        for (auto& t : targets)
            if (!lit.count(t)) goals.insert(t);
        int bestScore = INT_MIN;
        XGrid bestG;
        std::set<XPos> bestLit;
        int bestAdded = 0;
        for (auto& tgt : goals) {
            for (int arr_dir = 0; arr_dir < 4; arr_dir++) {
                int back_dir = OPP[arr_dir];
                int r = tgt.first + XD_DR[back_dir];
                int c = tgt.second + XD_DC[back_dir];
                while (r >= 0 && r < Hh && c >= 0 && c < Ww) {
                    char ch = cur[r][c];
                    if (ch == '#' || ch == '/' || ch == '\\') break;
                    if (fwd.count({r, c}) && ch == '.') {
                        for (char mir : {'/', '\\'}) {
                            XGrid ng = cur;
                            ng[r][c] = mir;
                            std::set<XPos> nlit = xd_trace(ng, lasers);
                            if (!nlit.count(tgt)) { r += XD_DR[back_dir]; c += XD_DC[back_dir]; continue; }
                            int tlit = 0;
                            int newly = 0;
                            for (auto& p : nlit) if (targets.count(p)) tlit++;
                            for (auto& p : nlit) if (!lit.count(p)) newly++;
                            int score = tlit * 1000 + newly;
                            if (score > bestScore) { bestScore = score; bestG = ng; bestLit = nlit; bestAdded = 1; }
                        }
                    }
                    r += XD_DR[back_dir];
                    c += XD_DC[back_dir];
                }
            }
        }
        if (bestScore == INT_MIN) break;
        int prevlit = 0;
        int newlit = 0;
        for (auto& p : lit) if (targets.count(p)) prevlit++;
        for (auto& p : bestLit) if (targets.count(p)) newlit++;
        if (newlit <= prevlit) break;
        cur = bestG;
        lit = bestLit;
        used += bestAdded;
    }
    bool allit = true;
    for (auto& t : targets)
        if (!lit.count(t)) { allit = false; break; }
    if (allit && used <= L) { xd_commit(cur); return true; }
    return false;
}

/*
 xd_coverage_solve sklada lustro na polu ktore maksymalizuje liczbe oswietlonych celow.
 Kryterium to litcnt*10000 + rozmiar wiazki zeby faworyzowac szerokie wiazki.
*/
static bool xd_coverage_solve(clock_t dl) {
    XGrid g;
    std::vector<XLaser> lasers;
    std::set<XPos> targets;
    xd_parse(g, lasers, targets);
    if (targets.empty()) return true;

    int Hh = H;
    int Ww = W;

    auto count_beam = [&](const XGrid& gg) -> std::pair<int,int> {
        std::set<std::pair<int,int>> cells;
        std::set<std::tuple<int,int,int>> vis;
        int tlit = 0;
        for (auto& laser : lasers) {
            int r = laser.r + XD_DR[laser.dir];
            int c = laser.c + XD_DC[laser.dir];
            int dir = laser.dir;
            while (r >= 0 && r < Hh && c >= 0 && c < Ww) {
                auto st = std::make_tuple(r, c, dir);
                if (vis.count(st)) break;
                vis.insert(st);
                char ch = gg[r][c];
                if (ch == '#') break;
                if (ch == 'O') { if (!cells.count({r, c})) tlit++; }
                cells.insert({r, c});
                if (ch == '/' || ch == '\\') dir = xd_reflect(dir, ch);
                r += XD_DR[dir];
                c += XD_DC[dir];
            }
        }
        return {(int)cells.size(), tlit};
    };

    auto get_beam_cells = [&](const XGrid& gg) -> std::set<std::pair<int,int>> {
        std::set<std::pair<int,int>> cells;
        std::set<std::tuple<int,int,int>> vis;
        for (auto& laser : lasers) {
            int r = laser.r + XD_DR[laser.dir];
            int c = laser.c + XD_DC[laser.dir];
            int dir = laser.dir;
            while (r >= 0 && r < Hh && c >= 0 && c < Ww) {
                auto st = std::make_tuple(r, c, dir);
                if (vis.count(st)) break;
                vis.insert(st);
                char ch = gg[r][c];
                if (ch == '#') break;
                cells.insert({r, c});
                if (ch == '/' || ch == '\\') dir = xd_reflect(dir, ch);
                r += XD_DR[dir];
                c += XD_DC[dir];
            }
        }
        return cells;
    };

    XGrid cur = g;
    int used = 0;
    for (auto& row : cur)
        for (char ch : row)
            if (ch == '/' || ch == '\\') used++;
    auto [initCells, initTlit] = count_beam(cur);
    if (initTlit == (int)targets.size()) { xd_commit(cur); return true; }
    while (used < L) {
        if (clock() >= dl) return false;
        auto beamCells = get_beam_cells(cur);
        int bestScore = -1;
        int bestR = -1;
        int bestC = -1;
        char bestMir = 0;
        for (auto& [br, bc] : beamCells) {
            if (cur[br][bc] != '.') continue;
            for (char mir : {'/', '\\'}) {
                XGrid ng = cur;
                ng[br][bc] = mir;
                auto [nc, nt] = count_beam(ng);
                int score = nt * 10000 + nc;
                if (score > bestScore) { bestScore = score; bestR = br; bestC = bc; bestMir = mir; }
            }
        }
        if (bestR < 0) break;
        cur[bestR][bestC] = bestMir;
        used++;
        auto [nc, nt] = count_beam(cur);
        if (nt == (int)targets.size()) { xd_commit(cur); return true; }
    }
    return false;
}

/*
 xd_coverage_random dziala jak xd_coverage_solve ale losowo probkuje pola wiazki.
 Daje roznorodnosc przez wybor sposrod top-3 kandydatow z losowym przesuniecie.
*/
static bool xd_coverage_random(clock_t dl) {
    XGrid g;
    std::vector<XLaser> lasers;
    std::set<XPos> targets;
    xd_parse(g, lasers, targets);
    if (targets.empty()) return true;

    int Hh = H;
    int Ww = W;

    auto get_beam_info = [&](const XGrid& gg) -> std::pair<std::set<std::pair<int,int>>, int> {
        std::set<std::pair<int,int>> cells;
        std::set<std::tuple<int,int,int>> vis;
        int tlit = 0;
        for (auto& laser : lasers) {
            int r = laser.r + XD_DR[laser.dir];
            int c = laser.c + XD_DC[laser.dir];
            int dir = laser.dir;
            while (r >= 0 && r < Hh && c >= 0 && c < Ww) {
                auto st = std::make_tuple(r, c, dir);
                if (vis.count(st)) break;
                vis.insert(st);
                char ch = gg[r][c];
                if (ch == '#') break;
                if (ch == 'O') { if (!cells.count({r, c})) tlit++; }
                cells.insert({r, c});
                if (ch == '/' || ch == '\\') dir = xd_reflect(dir, ch);
                r += XD_DR[dir];
                c += XD_DC[dir];
            }
        }
        return {cells, tlit};
    };

    uint64_t rng = 0xFEEDFACE98765432ULL ^ (uint64_t)clock();
    auto rng_next = [&]() -> uint64_t {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        return rng;
    };

    while (clock() < dl) {
        XGrid cur = g;
        int used = 0;
        for (auto& row : cur)
            for (char ch : row)
                if (ch == '/' || ch == '\\') used++;
        while (used < L) {
            if (clock() >= dl) return false;
            auto [beamCells, tlit] = get_beam_info(cur);
            if (tlit == (int)targets.size()) { xd_commit(cur); return true; }
            std::vector<std::pair<int,int>> empties;
            for (auto& [br, bc] : beamCells)
                if (cur[br][bc] == '.') empties.push_back({br, bc});
            if (empties.empty()) break;
            std::vector<std::tuple<int,int,int,char>> scored;
            int sample = std::min((int)empties.size(), 20);
            for (int i = 0; i < sample; i++) {
                int j = i + rng_next() % (empties.size() - i);
                std::swap(empties[i], empties[j]);
                auto [br, bc] = empties[i];
                for (char mir : {'/', '\\'}) {
                    XGrid ng = cur;
                    ng[br][bc] = mir;
                    auto [ncells, nt] = get_beam_info(ng);
                    int score = nt * 10000 + (int)ncells.size();
                    scored.push_back({score, br, bc, mir});
                }
            }
            if (scored.empty()) break;
            std::sort(scored.begin(), scored.end(), std::greater<>());
            int topN = std::min((int)scored.size(), 3);
            int pick = rng_next() % topN;
            auto [sc, br, bc, mir] = scored[pick];
            cur[br][bc] = mir;
            used++;
            auto [nc2, nt2] = get_beam_info(cur);
            if (nt2 == (int)targets.size()) { xd_commit(cur); return true; }
        }
    }
    return false;
}

static const int RD_DR[] = {-1, 0, 1, 0};
static const int RD_DC[] = {0, 1, 0, -1};
static const int RD_SLASH[] = {1, 0, 3, 2};
static const int RD_BACKSLASH[] = {3, 2, 1, 0};

static int rd_rdir(int d, char m) {
    return m == '/' ? RD_SLASH[d] : RD_BACKSLASH[d];
}

struct RDLaser { int r, c, dir; };
static std::vector<RDLaser> rd_lasers;
static std::vector<std::pair<int,int>> rd_targets;
static int rd_ntargets;
using RG2 = std::vector<std::vector<char>>;

static void rd_parse(RG2& g) {
    g.assign(H, std::vector<char>(W));
    for (int r = 0; r < H; r++)
        for (int c = 0; c < W; c++)
            g[r][c] = grid[r * W + c];
    const char lc[] = "A>V<";
    const int ld[] = {0, 1, 2, 3};
    for (int r = 0; r < H; r++) {
        for (int c = 0; c < W; c++) {
            char ch = g[r][c];
            for (int i = 0; i < 4; i++) {
                if (ch == lc[i]) {
                    RDLaser l;
                    l.r = r;
                    l.c = c;
                    l.dir = ld[i];
                    rd_lasers.push_back(l);
                }
            }
            if (ch == 'O') rd_targets.push_back({r, c});
        }
    }
}

static void rd_commit(const RG2& g) {
    for (int r = 0; r < H; r++)
        for (int c = 0; c < W; c++)
            grid[r * W + c] = g[r][c];
}

static std::vector<uint32_t> rd_dv;
static uint32_t rd_dg = 0;

struct RDFT { std::vector<int> cells; int tlit; };

static RDFT rd_ftrace(const RG2& g) {
    if ((int)rd_dv.size() < W * H * 4) rd_dv.assign(W * H * 4, 0);
    ++rd_dg;
    RDFT ft;
    ft.tlit = 0;
    static std::vector<uint32_t> cv;
    static uint32_t cg = 0;
    if ((int)cv.size() < W * H) cv.assign(W * H, 0);
    ++cg;
    static std::vector<uint32_t> ov;
    static uint32_t og = 0;
    if ((int)ov.size() < W * H) ov.assign(W * H, 0);
    ++og;
    for (auto& laser : rd_lasers) {
        int r = laser.r + RD_DR[laser.dir];
        int c = laser.c + RD_DC[laser.dir];
        int dir = laser.dir;
        while (r >= 0 && r < H && c >= 0 && c < W) {
            int idx = r * W + c;
            int didx = idx * 4 + dir;
            if (rd_dv[didx] == rd_dg) break;
            rd_dv[didx] = rd_dg;
            char ch = g[r][c];
            if (ch == '#') break;
            if (cv[idx] != cg) { cv[idx] = cg; ft.cells.push_back(idx); }
            if (ch == 'O' && ov[idx] != og) { ov[idx] = og; ft.tlit++; }
            if (ch == '/' || ch == '\\') dir = rd_rdir(dir, ch);
            r += RD_DR[dir];
            c += RD_DC[dir];
        }
    }
    return ft;
}

static bool rd_solved(const RG2& g) {
    return rd_ftrace(g).tlit == rd_ntargets;
}

static int rd_score(const RG2& g) {
    auto ft = rd_ftrace(g);
    return ft.tlit * 100000 + (int)ft.cells.size();
}

static uint64_t rd_rng = 0xCAFEBABEULL;
static uint64_t rd_rng_next() {
    rd_rng ^= rd_rng << 13;
    rd_rng ^= rd_rng >> 7;
    rd_rng ^= rd_rng << 17;
    return rd_rng;
}

static std::vector<uint32_t> rd_fv;
static uint32_t rd_fg = 0;

static void rd_build_fwd(const RG2& g) {
    int N = W * H * 4;
    if ((int)rd_fv.size() < N) rd_fv.assign(N, 0);
    ++rd_fg;
    static std::vector<uint32_t> sdv;
    static uint32_t sdg = 0;
    if ((int)sdv.size() < N) sdv.assign(N, 0);
    ++sdg;
    for (auto& laser : rd_lasers) {
        int r = laser.r + RD_DR[laser.dir];
        int c = laser.c + RD_DC[laser.dir];
        int dir = laser.dir;
        while (r >= 0 && r < H && c >= 0 && c < W) {
            int idx = r * W + c;
            int didx = idx * 4 + dir;
            if (sdv[didx] == sdg) break;
            sdv[didx] = sdg;
            char ch = g[r][c];
            if (ch == '#') break;
            rd_fv[didx] = rd_fg;
            if (ch == '/' || ch == '\\') dir = rd_rdir(dir, ch);
            r += RD_DR[dir];
            c += RD_DC[dir];
        }
    }
}

struct RDMir { int r, c; char m; };

static std::vector<RDMir> rd_search(const RG2& g0, int tr, int tc, int budget, clock_t dl) {
    int N = H * W * 4;
    static std::vector<int> dist;
    static std::vector<uint32_t> dep;
    static uint32_t ep = 0;
    static std::vector<int> par_e, par_r, par_c;
    static std::vector<char> par_m;
    static std::vector<bool> par_pl;
    ++ep;
    if ((int)dist.size() < N) {
        dist.resize(N);
        dep.resize(N, 0);
        par_e.resize(N);
        par_r.resize(N);
        par_c.resize(N);
        par_m.resize(N);
        par_pl.resize(N);
    }
    auto enc = [](int r, int c, int d) { return (r * W + c) * 4 + d; };
    auto get_d = [&](int e) -> int { return dep[e] == ep ? dist[e] : INT_MAX; };
    auto set_d = [&](int e, int v, int pe, int pr, int pc, char pm, bool pl) {
        dep[e] = ep;
        dist[e] = v;
        par_e[e] = pe;
        par_r[e] = pr;
        par_c[e] = pc;
        par_m[e] = pm;
        par_pl[e] = pl;
    };

    using T3 = std::tuple<int,int,int>;
    std::priority_queue<T3, std::vector<T3>, std::greater<T3>> pq;
    int serial = 0;

    auto push = [&](int cost, int r, int c, int dir, int pe, int pr, int pc, char pm, bool pl) {
        if (cost > budget || r < 0 || r >= H || c < 0 || c >= W) return;
        int e = enc(r, c, dir);
        if (get_d(e) <= cost) return;
        set_d(e, cost, pe, pr, pc, pm, pl);
        pq.push({cost, ++serial, e});
    };

    for (int arr_dir = 0; arr_dir < 4; arr_dir++) {
        int prev_r = tr - RD_DR[arr_dir];
        int prev_c = tc - RD_DC[arr_dir];
        if (prev_r >= 0 && prev_r < H && prev_c >= 0 && prev_c < W && g0[prev_r][prev_c] != '#')
            push(0, prev_r, prev_c, arr_dir, -1, 0, 0, 0, false);
    }

    while (!pq.empty()) {
        if (clock() >= dl) break;
        auto [cost, _s, e] = pq.top();
        pq.pop();
        if (get_d(e) < cost) continue;
        int r = (e / 4) / W;
        int c = (e / 4) % W;
        int dir = e & 3;
        if (rd_fv[e] == rd_fg) {
            std::vector<RDMir> res;
            int cur = e;
            while (cur != -1) {
                if (par_pl[cur]) res.push_back({par_r[cur], par_c[cur], par_m[cur]});
                cur = par_e[cur];
            }
            return res;
        }
        char ch = g0[r][c];
        if (ch == '#') continue;
        if (ch == '/' || ch == '\\') {
            int inc = rd_rdir(dir, ch);
            push(cost, r - RD_DR[inc], c - RD_DC[inc], inc, e, 0, 0, 0, false);
        } else {
            push(cost, r - RD_DR[dir], c - RD_DC[dir], dir, e, 0, 0, 0, false);
            if (ch == '.') {
                for (char m : {'/', '\\'}) {
                    int inc = rd_rdir(dir, m);
                    push(cost + 1, r - RD_DR[inc], c - RD_DC[inc], inc, e, r, c, m, true);
                }
            }
        }
    }
    return {};
}

/*
 fast_rev_greedy realizuje zachlanny krok dla fast_rev_solve: szuka najtanszej
 sciezki odwrotnej do nieoswietlonego celu i uklada potrzebne lustra.
*/
static bool fast_rev_greedy(RG2& g, int& used, clock_t dl) {
    for (int iter = 0; iter < L * 4 + 8 && used <= L; iter++) {
        if (clock() >= dl) return false;
        auto ft = rd_ftrace(g);
        if (ft.tlit == rd_ntargets) { rd_commit(g); return true; }
        rd_build_fwd(g);
        std::vector<bool> tlit_map(W * H, false);
        for (int idx : ft.cells) {
            int r = idx / W;
            int c = idx % W;
            if (g[r][c] == 'O') tlit_map[idx] = true;
        }
        int rem = L - used;
        int bestCost = INT_MAX;
        std::vector<RDMir> bestPl;
        for (auto& [tr, tc] : rd_targets) {
            if (tlit_map[tr * W + tc]) continue;
            if (rem <= 0) break;
            auto pl = rd_search(g, tr, tc, rem, dl);
            int cost = (int)pl.size();
            if (cost < bestCost) { bestCost = cost; bestPl = pl; }
        }
        if (bestCost == INT_MAX) break;
        for (auto& [r, c, m] : bestPl)
            if (g[r][c] == '.') { g[r][c] = m; used++; }
    }
    if (rd_solved(g)) { rd_commit(g); return true; }
    return false;
}

/*
 fast_rev_solve laczy szukanie odwrotne (Dijkstra od celu) z ILSem
 Usuwa losowo k luster i ponownie puszcza greedy, szukajac lepszego rozwiazania
*/
static bool fast_rev_solve(clock_t dl) {
    rd_lasers.clear();
    rd_targets.clear();
    RG2 g;
    rd_parse(g);
    rd_ntargets = (int)rd_targets.size();
    if (rd_ntargets == 0) return true;
    rd_dv.assign(W * H * 4, 0);
    rd_dg = 0;
    int used = 0;
    for (auto& row : g)
        for (char ch : row)
            if (ch == '/' || ch == '\\') used++;
    int bsc = rd_score(g);
    RG2 best = g;
    int best_u = used;
    {
        RG2 gg = g;
        int u = used;
        if (fast_rev_greedy(gg, u, clock() + (clock_t)(0.5 * CLOCKS_PER_SEC))) return true;
        int s = rd_score(gg);
        if (s > bsc) { bsc = s; best = gg; best_u = u; }
    }
    int no_imp = 0;
    while (clock() < dl) {
        RG2 g2 = best;
        int u = best_u;
        std::vector<std::pair<int,int>> pm;
        for (int r = 0; r < H; r++)
            for (int c = 0; c < W; c++)
                if (g2[r][c] == '/' || g2[r][c] == '\\') pm.push_back({r, c});
        int k = 1 + (int)(rd_rng_next() % std::max(1, no_imp / 5 + 1));
        if (k > 3) k = 3;
        for (int i = 0; i < k && !pm.empty(); i++) {
            int pi = rd_rng_next() % pm.size();
            g2[pm[pi].first][pm[pi].second] = '.';
            u--;
            pm.erase(pm.begin() + pi);
        }
        clock_t sub = std::min(dl, clock() + (clock_t)(0.25 * CLOCKS_PER_SEC));
        fast_rev_greedy(g2, u, sub);
        if (rd_solved(g2)) { rd_commit(g2); return true; }
        int s = rd_score(g2);
        if (s > bsc) { bsc = s; best = g2; best_u = u; no_imp = 0; }
        else no_imp++;
    }
    return false;
}

static int laserR, laserC, laserDR, laserDC;
static int nTargets;

static std::vector<uint64_t> zob[2];
static uint64_t curHash = 0;

static constexpr size_t FAIL_TABLE_BITS = 16;
static constexpr size_t FAIL_TABLE_SIZE = 1u << FAIL_TABLE_BITS;
static constexpr size_t FAIL_TABLE_MASK = FAIL_TABLE_SIZE - 1;

struct FailEntry { uint64_t key; int maxLeft; };
static FailEntry failTable[FAIL_TABLE_SIZE];

static inline void failInsert(uint64_t key, int left) {
    size_t idx = (size_t)key & FAIL_TABLE_MASK;
    for (int probe = 0; probe < 4; ++probe) {
        FailEntry& e = failTable[(idx + probe) & FAIL_TABLE_MASK];
        if (e.key == 0 || e.key == key) {
            e.key = key;
            if (left > e.maxLeft) e.maxLeft = left;
            return;
        }
    }
    failTable[idx] = {key, left};
}

static inline int failLookup(uint64_t key) {
    size_t idx = (size_t)key & FAIL_TABLE_MASK;
    for (int probe = 0; probe < 4; ++probe) {
        FailEntry& e = failTable[(idx + probe) & FAIL_TABLE_MASK];
        if (e.key == 0) return -1;
        if (e.key == key) return e.maxLeft;
    }
    return -1;
}

static uint64_t splitmix64(uint64_t x) {
    x += 0x9E3779B97F4A7C15ULL;
    x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL;
    x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL;
    return x ^ (x >> 31);
}

static clock_t deadline;
static bool timedOut;

static std::vector<int> litGen, seenGen, unlitList;
static std::vector<uint32_t> traceVis;
static uint32_t traceCounter = 0;
static int genId = 0;
static std::vector<int> emptyArena;

struct Seg { int r, c, dr, dc; };
static std::vector<Seg> segBuf;
static int segCount;

static int traceBeam(int empties_clear_to) {
    ++traceCounter;
    ++genId;
    segCount = 0;
    int litCount = 0;
    int r = laserR + laserDR;
    int c = laserC + laserDC;
    int dr = laserDR;
    int dc = laserDC;
    const int Wl = W;
    const int Hl = H;
    char* g = grid.data();
    uint32_t* tv = traceVis.data();
    int* lg = litGen.data();
    int* sg = seenGen.data();
    const uint32_t tc = traceCounter;
    const int gid = genId;
    segBuf[segCount++] = {r, c, dr, dc};
    while ((unsigned)r < (unsigned)Hl && (unsigned)c < (unsigned)Wl) {
        int idx = r * Wl + c;
        char ch = g[idx];
        if (ch == '#') break;
        int bit = (dr == -1) ? 0 : (dr == 1) ? 1 : (dc == -1) ? 2 : 3;
        uint32_t mask = 1u << bit;
        uint32_t v = tv[idx];
        if ((v >> 4) == tc) {
            if (v & mask) break;
            tv[idx] = v | mask;
        } else {
            tv[idx] = (tc << 4) | mask;
        }
        if (ch == '.') {
            if (sg[idx] != gid) { sg[idx] = gid; emptyArena.push_back(idx); }
        } else if (ch == '/') {
            int ndr = -dc;
            int ndc = -dr;
            dr = ndr;
            dc = ndc;
            segBuf[segCount++] = {r + dr, c + dc, dr, dc};
        } else if (ch == '\\') {
            int ndr = dc;
            int ndc = dr;
            dr = ndr;
            dc = ndc;
            segBuf[segCount++] = {r + dr, c + dc, dr, dc};
        } else if (ch == 'O') {
            if (lg[idx] != gid) { lg[idx] = gid; ++litCount; }
            emptyArena.resize(empties_clear_to);
        }
        r += dr;
        c += dc;
    }
    return litCount;
}

static inline bool pathClearH(int row, int c1, int c2) {
    int lo = std::min(c1, c2) + 1;
    int hi = std::max(c1, c2);
    for (int c = lo; c < hi; ++c) {
        char ch = grid[row * W + c];
        if (ch == '#' || ch == '/' || ch == '\\') return false;
    }
    return true;
}

static inline bool pathClearV(int col, int r1, int r2) {
    int lo = std::min(r1, r2) + 1;
    int hi = std::max(r1, r2);
    for (int r = lo; r < hi; ++r) {
        char ch = grid[r * W + col];
        if (ch == '#' || ch == '/' || ch == '\\') return false;
    }
    return true;
}

struct Cand { int cell; char type; };
static std::vector<Cand> tdCands[205];

/*
 buildTDCands buduje kandydatow na pozycje lustra skierowanych do nieoswietlonych celow.
 Rozpatruje kazdy segment wiazki i kazdy cel, szukajac przeciec wierszy i kolumn.
*/
static void buildTDCands(int depth) {
    auto& v = tdCands[depth];
    v.clear();
    const int* lg = litGen.data();
    const int gid = genId;
    for (int si = 0; si < segCount; ++si) {
        int sr = segBuf[si].r - segBuf[si].dr;
        int sc = segBuf[si].c - segBuf[si].dc;
        int dr = segBuf[si].dr;
        int dc = segBuf[si].dc;
        for (int ti : unlitList) {
            if (lg[ti] == gid) continue;
            int tr = ti / W;
            int tc_t = ti % W;
            if (dc == 0) {
                int mr = tr;
                int mc = sc;
                if ((unsigned)mr >= (unsigned)H || (unsigned)mc >= (unsigned)W) continue;
                if (grid[mr * W + mc] != '.') continue;
                if (dr > 0 && mr <= sr) continue;
                if (dr < 0 && mr >= sr) continue;
                if (!pathClearV(mc, sr, mr)) continue;
                int ndc_slash = -dr;
                int ndc_back = dr;
                if (ndc_slash > 0 && tc_t > mc && pathClearH(mr, mc, tc_t))
                    v.push_back({mr * W + mc, '/'});
                if (ndc_slash < 0 && tc_t < mc && pathClearH(mr, mc, tc_t))
                    v.push_back({mr * W + mc, '/'});
                if (ndc_back > 0 && tc_t > mc && pathClearH(mr, mc, tc_t))
                    v.push_back({mr * W + mc, '\\'});
                if (ndc_back < 0 && tc_t < mc && pathClearH(mr, mc, tc_t))
                    v.push_back({mr * W + mc, '\\'});
            } else {
                int mr = sr;
                int mc = tc_t;
                if ((unsigned)mr >= (unsigned)H || (unsigned)mc >= (unsigned)W) continue;
                if (grid[mr * W + mc] != '.') continue;
                if (dc > 0 && mc <= sc) continue;
                if (dc < 0 && mc >= sc) continue;
                if (!pathClearH(mr, sc, mc)) continue;
                int ndr_slash = -dc;
                int ndr_back = dc;
                if (ndr_slash < 0 && tr < mr && pathClearV(mc, mr, tr))
                    v.push_back({mr * W + mc, '/'});
                if (ndr_slash > 0 && tr > mr && pathClearV(mc, mr, tr))
                    v.push_back({mr * W + mc, '/'});
                if (ndr_back > 0 && tr > mr && pathClearV(mc, mr, tr))
                    v.push_back({mr * W + mc, '\\'});
                if (ndr_back < 0 && tr < mr && pathClearV(mc, mr, tr))
                    v.push_back({mr * W + mc, '\\'});
            }
        }
    }
    std::sort(v.begin(), v.end(), [](const Cand& a, const Cand& b) {
        return a.cell < b.cell || (a.cell == b.cell && a.type < b.type);
    });
    v.erase(std::unique(v.begin(), v.end(), [](const Cand& a, const Cand& b) {
        return a.cell == b.cell && a.type == b.type;
    }), v.end());
}

struct Frame {
    int empties_start;
    int empties_end;
    int next_i;
    int next_orient;
    int last_placed;
    bool needs_trace;
    int td_i;
    bool td_done;
};
static std::vector<Frame> stk;

/*
 solveT1 to backtracker probujacy ukladac lustra na kazdym pustym polu wiazki.
 Uzywa tablicy failTable z hashowaniem Zobrista do przycinania powtarzajacych sie stanow.
*/
static bool solveT1() {
    stk.clear();
    emptyArena.clear();
    curHash = 0;
    timedOut = false;
    stk.push_back({0, 0, 0, 0, -1, true, 0, true});
    int checkTimer = 0;
    while (!stk.empty()) {
        if (++checkTimer >= 4096) {
            checkTimer = 0;
            if (clock() >= deadline) { timedOut = true; return false; }
        }
        Frame& f = stk.back();
        int depth = (int)stk.size() - 1;
        if (f.needs_trace) {
            int start = (int)emptyArena.size();
            f.empties_start = start;
            int litCount = traceBeam(start);
            f.empties_end = (int)emptyArena.size();
            f.next_i = 0;
            f.next_orient = 0;
            f.last_placed = -1;
            f.needs_trace = false;
            if (litCount == nTargets) return true;
            int left = L - depth;
            if (left <= 0) { f.next_i = f.empties_end - f.empties_start; continue; }
            int cached = failLookup(curHash);
            if (cached >= left) { f.next_i = f.empties_end - f.empties_start; continue; }
        }
        if (f.last_placed >= 0) {
            if (f.next_orient == 1) {
                int p = f.last_placed;
                curHash ^= zob[0][p];
                grid[p] = '\\';
                curHash ^= zob[1][p];
                f.next_orient = 2;
                stk.push_back({0, 0, 0, 0, -1, true, 0, true});
                continue;
            } else {
                int p = f.last_placed;
                curHash ^= zob[1][p];
                grid[p] = '.';
                f.last_placed = -1;
                f.next_i++;
                f.next_orient = 0;
            }
        }
        int count = f.empties_end - f.empties_start;
        bool pushed = false;
        while (f.next_i < count) {
            int idx = emptyArena[f.empties_start + f.next_i];
            if (grid[idx] != '.') { f.next_i++; continue; }
            grid[idx] = '/';
            curHash ^= zob[0][idx];
            f.last_placed = idx;
            f.next_orient = 1;
            stk.push_back({0, 0, 0, 0, -1, true, 0, true});
            pushed = true;
            break;
        }
        if (!pushed) {
            int left = L - depth;
            if (left > 0) failInsert(curHash, left);
            emptyArena.resize(f.empties_start);
            stk.pop_back();
        }
    }
    return false;
}

/*
 solveT2 rozszerza solveT1 o liste kandydatow TD jako priorytet przed petla po wszystkich polach.
 Kandydaci TD sa wybierani zeby szybciej osiagnac nieoswietlone cele.
*/
static bool solveT2() {
    stk.clear();
    emptyArena.clear();
    curHash = 0;
    timedOut = false;
    stk.push_back({0, 0, 0, 0, -1, true, 0, false});
    int checkTimer = 0;
    while (!stk.empty()) {
        if (++checkTimer >= 4096) {
            checkTimer = 0;
            if (clock() >= deadline) { timedOut = true; return false; }
        }
        Frame& f = stk.back();
        int depth = (int)stk.size() - 1;
        if (f.needs_trace) {
            int start = (int)emptyArena.size();
            f.empties_start = start;
            int litCount = traceBeam(start);
            f.empties_end = (int)emptyArena.size();
            f.next_i = 0;
            f.next_orient = 0;
            f.last_placed = -1;
            f.needs_trace = false;
            f.td_i = 0;
            f.td_done = false;
            if (litCount == nTargets) return true;
            int left = L - depth;
            if (left <= 0) { f.next_i = f.empties_end - f.empties_start; f.td_done = true; continue; }
            int cached = failLookup(curHash);
            if (cached >= left) { f.next_i = f.empties_end - f.empties_start; f.td_done = true; continue; }
            buildTDCands(depth);
        }
        if (!f.td_done) {
            auto& tdc = tdCands[depth];
            if (f.last_placed >= 0) {
                int p = f.last_placed;
                char tp = tdc[f.td_i - 1].type;
                curHash ^= (tp == '/') ? zob[0][p] : zob[1][p];
                grid[p] = '.';
                f.last_placed = -1;
            }
            bool pushed = false;
            while (f.td_i < (int)tdc.size()) {
                auto& cd = tdc[f.td_i++];
                if (grid[cd.cell] != '.') continue;
                uint64_t h0 = (cd.type == '/') ? zob[0][cd.cell] : zob[1][cd.cell];
                grid[cd.cell] = cd.type;
                curHash ^= h0;
                f.last_placed = cd.cell;
                stk.push_back({0, 0, 0, 0, -1, true, 0, false});
                pushed = true;
                break;
            }
            if (!pushed) { f.td_done = true; f.last_placed = -1; }
            else continue;
        }
        if (f.last_placed >= 0) {
            if (f.next_orient == 1) {
                int p = f.last_placed;
                curHash ^= zob[0][p];
                grid[p] = '\\';
                curHash ^= zob[1][p];
                f.next_orient = 2;
                stk.push_back({0, 0, 0, 0, -1, true, 0, false});
                continue;
            } else {
                int p = f.last_placed;
                curHash ^= zob[1][p];
                grid[p] = '.';
                f.last_placed = -1;
                f.next_i++;
                f.next_orient = 0;
            }
        }
        int count = f.empties_end - f.empties_start;
        bool pushed = false;
        while (f.next_i < count) {
            int idx = emptyArena[f.empties_start + f.next_i];
            if (grid[idx] != '.') { f.next_i++; continue; }
            grid[idx] = '/';
            curHash ^= zob[0][idx];
            f.last_placed = idx;
            f.next_orient = 1;
            stk.push_back({0, 0, 0, 0, -1, true, 0, false});
            pushed = true;
            break;
        }
        if (!pushed) {
            int left = L - depth;
            if (left > 0) failInsert(curHash, left);
            emptyArena.resize(f.empties_start);
            stk.pop_back();
        }
    }
    return false;
}

/*
 H4 to zachlanny solver oparty na BFS 0-1 (deque) szukajacy najtanszej sciezki do kazdego kota.
 Iteruje po kotach i dla kazdego uklada lustra wzdluz znalezionej sciezki.
*/
namespace H4 {
    static const int INF = 1e9;
    static int dr[4] = {-1, 0, 1, 0};
    static int dc[4] = {0, 1, 0, -1};

    static int reflectDir(char m, int d) {
        if (m == '/') {
            static int r[4] = {1, 0, 3, 2};
            return r[d];
        } else {
            static int r[4] = {3, 2, 1, 0};
            return r[d];
        }
    }

    static int laserDir(char c) {
        if (c == 'A') return 0;
        if (c == '>') return 1;
        if (c == 'V') return 2;
        if (c == '<') return 3;
        return -1;
    }

    static bool isLaser(char c) {
        return c == 'A' || c == 'V' || c == '<' || c == '>';
    }

    static bool solve(clock_t deadline) {
        int gW = ::W;
        int gH = ::H;
        int gL = ::L;
        std::vector<std::string> board(gH);
        for (int r = 0; r < gH; r++) {
            board[r].resize(gW);
            for (int c = 0; c < gW; c++)
                board[r][c] = ::grid[r * gW + c];
        }
        int N = gW * gH;
        int S = 4 * N;
        int sr = -1;
        int sc = -1;
        int sd = -1;
        std::vector<int> cats;
        for (int r = 0; r < gH; r++) {
            for (int c = 0; c < gW; c++) {
                char ch = board[r][c];
                if (isLaser(ch) && sr == -1) { sr = r; sc = c; sd = laserDir(ch); }
                if (ch == 'O') cats.push_back(r * gW + c);
            }
        }
        if (sr < 0) return false;
        std::vector<unsigned char> lit(N, 0);
        std::vector<unsigned char> touched(N, 0);
        std::vector<unsigned char> usedState(S, 0);
        int remainingCats = (int)cats.size();
        int mirrorsUsed = 0;
        auto stateId = [&](int cell, int dir) { return cell * 4 + dir; };
        int startCell = sr * gW + sc;
        int currentState = stateId(startCell, sd);
        touched[startCell] = 1;
        usedState[currentState] = 1;
        std::vector<int> dist(S);
        std::vector<int> parent(S);
        std::vector<char> action(S);
        auto markCell = [&](int cell) {
            touched[cell] = 1;
            int r = cell / gW;
            int c = cell % gW;
            if (board[r][c] == 'O' && !lit[cell]) {
                lit[cell] = 1;
                remainingCats--;
            }
        };
        while (remainingCats > 0 && mirrorsUsed <= gL) {
            if (clock() >= deadline) return false;
            std::fill(dist.begin(), dist.end(), INF);
            std::fill(parent.begin(), parent.end(), -1);
            std::fill(action.begin(), action.end(), 0);
            std::deque<int> q;
            dist[currentState] = 0;
            q.push_front(currentState);
            while (!q.empty()) {
                int s = q.front();
                q.pop_front();
                int cell = s / 4;
                int dir = s % 4;
                int r = cell / gW;
                int c = cell % gW;
                if (dist[s] > gL - mirrorsUsed) continue;
                auto relax = [&](int outDir, char act, int cost) {
                    int nr = r + dr[outDir];
                    int nc = c + dc[outDir];
                    if (nr < 0 || nr >= gH || nc < 0 || nc >= gW) return;
                    if (board[nr][nc] == '#') return;
                    int ncell = nr * gW + nc;
                    int ns = stateId(ncell, outDir);
                    if (usedState[ns]) return;
                    int nd = dist[s] + cost;
                    if (nd < dist[ns] && mirrorsUsed + nd <= gL) {
                        dist[ns] = nd;
                        parent[ns] = s;
                        action[ns] = act;
                        if (cost == 0) q.push_front(ns);
                        else q.push_back(ns);
                    }
                };
                char ch = board[r][c];
                if (ch == '/' || ch == '\\') {
                    relax(reflectDir(ch, dir), 0, 0);
                } else {
                    relax(dir, 0, 0);
                    if (ch == '.') {
                        bool canPlaceHere = (!touched[cell] || s == currentState);
                        if (canPlaceHere && mirrorsUsed + dist[s] + 1 <= gL) {
                            relax(reflectDir('/', dir), '/', 1);
                            relax(reflectDir('\\', dir), '\\', 1);
                        }
                    }
                }
            }
            int bestState = -1;
            int bestCost = INF;
            for (int cat : cats) {
                if (lit[cat]) continue;
                for (int d = 0; d < 4; d++) {
                    int s = stateId(cat, d);
                    if (dist[s] < bestCost) { bestCost = dist[s]; bestState = s; }
                }
            }
            if (bestState == -1) break;
            if (bestCost == INF) break;
            std::vector<int> pathStates;
            std::vector<char> pathActions;
            int v = bestState;
            int guard = 0;
            while (v != currentState) {
                if (v < 0 || v >= S) return false;
                if (++guard > S) return false;
                pathStates.push_back(v);
                pathActions.push_back(action[v]);
                v = parent[v];
            }
            std::reverse(pathStates.begin(), pathStates.end());
            std::reverse(pathActions.begin(), pathActions.end());
            int prev = currentState;
            for (size_t i = 0; i < pathStates.size(); i++) {
                char act = pathActions[i];
                int pcell = prev / 4;
                int pr = pcell / gW;
                int pc = pcell % gW;
                if (act == '/' || act == '\\') {
                    if (board[pr][pc] == '.') { board[pr][pc] = act; mirrorsUsed++; }
                }
                int ns = pathStates[i];
                int ncell = ns / 4;
                usedState[ns] = 1;
                markCell(ncell);
                prev = ns;
            }
            currentState = bestState;
        }
        if (remainingCats != 0) return false;
        for (int r = 0; r < gH; r++)
            for (int c = 0; c < gW; c++)
                ::grid[r * gW + c] = board[r][c];
        return true;
    }
}

/*
 H6 to solver wielotryby z perturbacjami: uruchamia solveGreedy w kilku trybach
 (min koszt, max lustra, losowy) i zachowuje najlepsze rozwiazanie.
*/
namespace H6 {
    static const int INF = 1e9;
    static int gW, gH, gL, gN, gS;
    static std::vector<std::string> baseG;
    static std::vector<int> cats, catIdx;
    static int laserR = -1;
    static int laserC = -1;
    static int laserD = -1;
    static int dr[4] = {-1, 0, 1, 0};
    static int dc[4] = {0, 1, 0, -1};

    static bool isMirror(char c) { return c == '/' || c == '\\'; }
    static bool isLaser(char c) { return c == 'A' || c == 'V' || c == '<' || c == '>'; }
    static int laserDir(char c) {
        if (c == 'A') return 0;
        if (c == '>') return 1;
        if (c == 'V') return 2;
        return 3;
    }
    static int reflectDir(char m, int d) {
        if (m == '/') {
            static int r[4] = {1, 0, 3, 2};
            return r[d];
        } else {
            static int r[4] = {3, 2, 1, 0};
            return r[d];
        }
    }
    static int cellId(int r, int c) { return r * gW + c; }
    static int stateId(int cell, int dir) { return cell * 4 + dir; }
    static bool inside(int r, int c) { return r >= 0 && r < gH && c >= 0 && c < gW; }

    struct SimResult {
        int litCount = 0;
        std::vector<unsigned char> lit;
        std::vector<unsigned char> onPath;
        std::vector<int> path;
    };

    static SimResult simulateBoard(const std::vector<std::string>& g) {
        SimResult res;
        res.lit.assign(gN, 0);
        res.onPath.assign(gN, 0);
        std::vector<unsigned char> seen(gS, 0);
        int st = stateId(cellId(laserR, laserC), laserD);
        while (true) {
            if (seen[st]) break;
            seen[st] = 1;
            int cell = st / 4;
            int dir = st % 4;
            int r = cell / gW;
            int c = cell % gW;
            res.path.push_back(st);
            res.onPath[cell] = 1;
            if (g[r][c] == 'O' && !res.lit[cell]) { res.lit[cell] = 1; res.litCount++; }
            int nd = dir;
            if (isMirror(g[r][c])) nd = reflectDir(g[r][c], dir);
            int nr = r + dr[nd];
            int nc = c + dc[nd];
            if (!inside(nr, nc)) break;
            if (g[nr][nc] == '#') break;
            st = stateId(cellId(nr, nc), nd);
        }
        return res;
    }

    static int countMirrors(const std::vector<std::string>& g) {
        int ans = 0;
        for (int r = 0; r < gH; r++)
            for (int c = 0; c < gW; c++)
                if (isMirror(g[r][c])) ans++;
        return ans;
    }

    static void removeUnused(std::vector<std::string>& g) {
        SimResult sim = simulateBoard(g);
        for (int r = 0; r < gH; r++) {
            for (int c = 0; c < gW; c++) {
                int cell = cellId(r, c);
                if (isMirror(g[r][c]) && !sim.onPath[cell]) g[r][c] = '.';
            }
        }
    }

    static bool validBoard(const std::vector<std::string>& g) {
        if (countMirrors(g) > gL) return false;
        return simulateBoard(g).litCount == (int)cats.size();
    }

    struct Sol { bool ok = false; int lit = 0; std::vector<std::string> g; };
    struct BFSData {
        std::vector<int> dist;
        std::vector<int> parent;
        std::vector<char> action;
    };

    static BFSData runLocalBFS(const std::vector<std::string>& g, const SimResult& sim, int budget) {
        BFSData bfs;
        bfs.dist.assign(gS, INF);
        bfs.parent.assign(gS, -2);
        bfs.action.assign(gS, 0);
        std::deque<int> q;
        for (int st : sim.path) {
            if (bfs.dist[st] == 0) continue;
            bfs.dist[st] = 0;
            bfs.parent[st] = -1;
            q.push_back(st);
        }
        while (!q.empty()) {
            int st = q.front();
            q.pop_front();
            int cell = st / 4;
            int dir = st % 4;
            int r = cell / gW;
            int c = cell % gW;
            int base = bfs.dist[st];
            if (base > budget) continue;
            auto add = [&](int nd, int cost, char act) {
                if (base + cost > budget) return;
                int nr = r + dr[nd];
                int nc = c + dc[nd];
                if (!inside(nr, nc)) return;
                if (g[nr][nc] == '#') return;
                int ncell = cellId(nr, nc);
                int ns = stateId(ncell, nd);
                int ndist = base + cost;
                if (ndist < bfs.dist[ns]) {
                    bfs.dist[ns] = ndist;
                    bfs.parent[ns] = st;
                    bfs.action[ns] = act;
                    if (cost == 0) q.push_front(ns);
                    else q.push_back(ns);
                }
            };
            char ch = g[r][c];
            if (isMirror(ch)) {
                add(reflectDir(ch, dir), 0, 0);
                char other = ch == '/' ? '\\' : '/';
                add(reflectDir(other, dir), 0, other);
            } else {
                add(dir, 0, 0);
                if (ch == '.') {
                    add(reflectDir('/', dir), 1, '/');
                    add(reflectDir('\\', dir), 1, '\\');
                }
            }
        }
        return bfs;
    }

    static bool buildChanges(int target, const BFSData& bfs, std::vector<std::pair<int,char>>& changes) {
        changes.clear();
        std::vector<std::pair<int,char>> raw;
        int v = target;
        int guard = 0;
        while (true) {
            if (v < 0 || v >= gS) return false;
            if (bfs.parent[v] == -1) break;
            if (bfs.parent[v] < -1) return false;
            int p = bfs.parent[v];
            char act = bfs.action[v];
            if (act == '/' || act == '\\') raw.push_back({p / 4, act});
            v = p;
            if (++guard > gS) return false;
        }
        std::reverse(raw.begin(), raw.end());
        for (auto& [cell, ch] : raw) {
            bool found = false;
            for (auto& x : changes) {
                if (x.first == cell) {
                    if (x.second != ch) return false;
                    found = true;
                    break;
                }
            }
            if (!found) changes.push_back({cell, ch});
        }
        return !changes.empty();
    }

    static bool applyChanges(
        std::vector<std::string>& g,
        const std::vector<std::pair<int,char>>& changes,
        std::vector<std::pair<int,char>>& oldValues,
        int& added)
    {
        oldValues.clear();
        added = 0;
        for (auto& [cell, ch] : changes) {
            int r = cell / gW;
            int c = cell % gW;
            char cur = g[r][c];
            if (cur == ch) continue;
            if (cur != '.' && !isMirror(cur)) {
                for (auto& [ocell, och] : oldValues) g[ocell / gW][ocell % gW] = och;
                return false;
            }
            oldValues.push_back({cell, cur});
            if (cur == '.') added++;
            g[r][c] = ch;
        }
        return true;
    }

    static void revertChanges(std::vector<std::string>& g, const std::vector<std::pair<int,char>>& oldValues) {
        for (auto& [cell, ch] : oldValues)
            g[cell / gW][cell % gW] = ch;
    }

    static Sol solveGreedy(int mode, uint64_t seed, std::chrono::steady_clock::time_point deadline) {
        std::mt19937_64 rng(seed);
        std::vector<std::string> g = baseG;
        Sol best;
        best.g = g;
        best.lit = simulateBoard(g).litCount;
        int maxIter = std::max(80, gL * 5 + 120);
        for (int iter = 0; iter < maxIter; iter++) {
            if ((iter & 7) == 0 && std::chrono::steady_clock::now() > deadline) break;
            removeUnused(g);
            SimResult sim = simulateBoard(g);
            if (sim.litCount > best.lit) { best.lit = sim.litCount; best.g = g; }
            if (sim.litCount == (int)cats.size() && countMirrors(g) <= gL) return {true, sim.litCount, g};
            int used = countMirrors(g);
            int budget = gL - used;
            if (budget < 0) break;
            BFSData bfs = runLocalBFS(g, sim, budget);
            struct Cand { int dist, state; };
            std::vector<Cand> cand;
            for (int cat : cats) {
                if (sim.lit[cat]) continue;
                for (int d = 0; d < 4; d++) {
                    int st = stateId(cat, d);
                    if (bfs.dist[st] <= budget) cand.push_back({bfs.dist[st], st});
                }
            }
            if (cand.empty()) break;
            if (mode == 0 || mode == 1)
                std::sort(cand.begin(), cand.end(), [](const Cand& a, const Cand& b) {
                    if (a.dist != b.dist) return a.dist < b.dist;
                    return a.state < b.state;
                });
            else if (mode == 2)
                std::sort(cand.begin(), cand.end(), [](const Cand& a, const Cand& b) {
                    if (a.dist != b.dist) return a.dist > b.dist;
                    return a.state < b.state;
                });
            else
                std::shuffle(cand.begin(), cand.end(), rng);
            int evalLimit;
            if (gN <= 1200) evalLimit = (int)cand.size();
            else if (gN <= 5000) evalLimit = std::min((int)cand.size(), 2500);
            else evalLimit = std::min((int)cand.size(), 1000);
            long long bestScore = LLONG_MIN;
            std::vector<std::pair<int,char>> bestChanges;
            for (int i = 0; i < evalLimit; i++) {
                std::vector<std::pair<int,char>> changes;
                if (!buildChanges(cand[i].state, bfs, changes)) continue;
                std::vector<std::pair<int,char>> oldValues;
                int added = 0;
                if (!applyChanges(g, changes, oldValues, added)) continue;
                if (used + added <= gL) {
                    int litNow = simulateBoard(g).litCount;
                    int mirrorsNow = countMirrors(g);
                    long long noise = (long long)(rng() % 1000);
                    long long score = 0;
                    if (mode == 0) score = (long long)litNow * 10000000LL - (long long)added * 20000LL - cand[i].dist * 100LL;
                    else if (mode == 1) score = (long long)litNow * 10000000LL - (long long)mirrorsNow * 10000LL - cand[i].dist * 20LL + noise;
                    else if (mode == 2) score = (long long)(litNow - sim.litCount) * 10000000LL - (long long)std::max(1, added) * 50000LL - cand[i].dist * 10LL + noise;
                    else score = (long long)litNow * 10000000LL - (long long)mirrorsNow * 5000LL + noise * 100LL;
                    bool allow = (mode < 3) ? (litNow >= sim.litCount) : (litNow + 2 >= sim.litCount);
                    if (allow && score > bestScore) { bestScore = score; bestChanges = changes; }
                }
                revertChanges(g, oldValues);
            }
            if (bestChanges.empty()) break;
            std::vector<std::pair<int,char>> oldValues;
            int added = 0;
            if (!applyChanges(g, bestChanges, oldValues, added)) break;
            if (countMirrors(g) > gL) { revertChanges(g, oldValues); break; }
            removeUnused(g);
            int nowLit = simulateBoard(g).litCount;
            if (nowLit > best.lit) { best.lit = nowLit; best.g = g; }
            if (nowLit == (int)cats.size() && countMirrors(g) <= gL) return {true, nowLit, g};
        }
        removeUnused(g);
        int lit = simulateBoard(g).litCount;
        if (lit > best.lit) { best.lit = lit; best.g = g; }
        if (lit == (int)cats.size() && countMirrors(g) <= gL) return {true, lit, g};
        return best;
    }

    static bool solve(clock_t cdeadline) {
        gW = ::W;
        gH = ::H;
        gL = ::L;
        gN = gW * gH;
        gS = 4 * gN;
        baseG.assign(gH, std::string(gW, '.'));
        for (int r = 0; r < gH; r++)
            for (int c = 0; c < gW; c++)
                baseG[r][c] = ::grid[r * gW + c];
        cats.clear();
        catIdx.assign(gN, -1);
        laserR = laserC = -1;
        laserD = 0;
        for (int r = 0; r < gH; r++) {
            for (int c = 0; c < gW; c++) {
                char ch = baseG[r][c];
                if (isLaser(ch)) { laserR = r; laserC = c; laserD = laserDir(ch); }
                if (ch == 'O') {
                    int id = cellId(r, c);
                    catIdx[id] = (int)cats.size();
                    cats.push_back(id);
                }
            }
        }
        if (laserR < 0) return false;
        auto deadline = std::chrono::steady_clock::now()
            + std::chrono::milliseconds((long long)((cdeadline - clock()) * 1000 / CLOCKS_PER_SEC));
        if (validBoard(baseG)) return true;
        Sol best;
        best.g = baseG;
        best.lit = simulateBoard(baseG).litCount;
        for (int attempt = 0; attempt < 80; attempt++) {
            if (std::chrono::steady_clock::now() > deadline) break;
            if (clock() >= cdeadline) break;
            int mode = attempt % 6;
            uint64_t seed = 123456789ULL + 1000003ULL * attempt;
            Sol cur = solveGreedy(mode, seed, deadline);
            if (cur.ok) {
                for (int r = 0; r < gH; r++)
                    for (int c = 0; c < gW; c++)
                        ::grid[r * gW + c] = cur.g[r][c];
                return true;
            }
            if (cur.lit > best.lit) best = cur;
        }
        return false;
    }
}

int main(int argc, char** argv) {
    if (argc >= 3) {
        if (!std::freopen(argv[1], "r", stdin)) return 1;
        if (!std::freopen(argv[2], "w", stdout)) return 1;
    }

    std::string input;
    {
        char buf[65536];
        size_t n;
        while ((n = std::fread(buf, 1, sizeof(buf), stdin)) > 0) input.append(buf, n);
    }
    size_t pos = 0;
    auto skipWS = [&]() {
        while (pos < input.size() && (input[pos] == ' ' || input[pos] == '\t' || input[pos] == '\r' || input[pos] == '\n'))
            ++pos;
    };
    auto readInt = [&]() {
        skipWS();
        int v = 0;
        while (pos < input.size() && input[pos] >= '0' && input[pos] <= '9')
            v = v * 10 + (input[pos++] - '0');
        return v;
    };
    W = readInt();
    H = readInt();
    L = readInt();
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

    laserR = laserC = -1;
    laserDR = laserDC = 0;
    nTargets = 0;
    for (int idx = 0; idx < W * H; ++idx) {
        char c = grid[idx];
        int r = idx / W;
        int cc = idx % W;
        switch (c) {
            case 'A': laserR = r; laserC = cc; laserDR = -1; laserDC = 0; break;
            case 'V': laserR = r; laserC = cc; laserDR = 1; laserDC = 0; break;
            case '<': laserR = r; laserC = cc; laserDR = 0; laserDC = -1; break;
            case '>': laserR = r; laserC = cc; laserDR = 0; laserDC = 1; break;
            case 'O': ++nTargets; break;
            default: break;
        }
    }

    litGen.assign((size_t)W * H, 0);
    seenGen.assign((size_t)W * H, 0);
    traceVis.assign((size_t)W * H, 0);
    segBuf.resize((size_t)W * H + 4);
    zob[0].resize((size_t)W * H);
    zob[1].resize((size_t)W * H);
    uint64_t seed = 0xC0FFEE123456ABCDULL ^ ((uint64_t)W * 31 + H);
    for (int i = 0; i < W * H; ++i) {
        seed = splitmix64(seed);
        zob[0][i] = seed | 1ULL;
        seed = splitmix64(seed);
        zob[1][i] = seed | 1ULL;
    }
    memset(failTable, 0, sizeof(failTable));
    stk.reserve((size_t)L + 4);
    emptyArena.reserve(1u << 14);
    for (int i = 0; i < W * H; ++i)
        if (grid[i] == 'O') unlitList.push_back(i);

    std::string gridBackup = grid;
    bool solved = false;

    clock_t T0 = clock();
    clock_t HARD = T0 + (clock_t)(9.0 * CLOCKS_PER_SEC);

    clock_t xdDL = clock() + (clock_t)(0.8 * CLOCKS_PER_SEC);
    try {
        if (xd_solve(xdDL)) solved = true;
    } catch (...) { solved = false; }
    if (!solved) {
        grid = gridBackup;
        deadline = clock() + (clock_t)(0.2 * CLOCKS_PER_SEC);
        if (solveT2()) solved = true;
        if (!solved) grid = gridBackup;
    }

    if (!solved) {
        clock_t dl = clock() + (clock_t)(0.4 * CLOCKS_PER_SEC);
        try { solved = H4::solve(dl); } catch (...) { solved = false; }
        if (!solved) grid = gridBackup;
    }
    if (!solved) {
        clock_t dl = clock() + (clock_t)(0.4 * CLOCKS_PER_SEC);
        try { solved = H6::solve(dl); } catch (...) { solved = false; }
        if (!solved) grid = gridBackup;
    }

    if (!solved) {
        clock_t dl = clock() + (clock_t)(2.5 * CLOCKS_PER_SEC);
        try { solved = fast_rev_solve(dl); } catch (...) { solved = false; }
        if (!solved) grid = gridBackup;
    }
    if (!solved) {
        clock_t dl = clock() + (clock_t)(0.15 * CLOCKS_PER_SEC);
        try { solved = xd_coverage_solve(dl); } catch (...) { solved = false; }
        if (!solved) grid = gridBackup;
    }
    if (!solved) {
        clock_t dl = clock() + (clock_t)(0.15 * CLOCKS_PER_SEC);
        try { solved = xd_reverse_solve(dl); } catch (...) { solved = false; }
        if (!solved) grid = gridBackup;
    }
    if (!solved) {
        clock_t dl = clock() + (clock_t)(0.5 * CLOCKS_PER_SEC);
        try { solved = xd_coverage_random(dl); } catch (...) { solved = false; }
        if (!solved) grid = gridBackup;
    }
    if (!solved) {
        clock_t dl = clock() + (clock_t)(0.3 * CLOCKS_PER_SEC);
        try { solved = xd_random_solve(dl); } catch (...) { solved = false; }
        if (!solved) grid = gridBackup;
    }

    if (!solved && clock() < HARD) {
        grid = gridBackup;
        memset(failTable, 0, sizeof(failTable));
        clock_t rem = HARD - clock();
        clock_t t2budget = std::min((clock_t)(1.5 * CLOCKS_PER_SEC), rem / 3);
        deadline = clock() + t2budget;
        if (solveT2()) {
            solved = true;
        } else if (timedOut && clock() < HARD) {
            grid = gridBackup;
            memset(failTable, 0, sizeof(failTable));
            deadline = HARD;
            if (solveT1()) solved = true;
        }
        if (!solved) grid = gridBackup;
    }

    std::printf("%d %d %d\n", W, H, L);
    for (int i = 0; i < H; ++i) {
        std::fwrite(grid.data() + (size_t)i * W, 1, W, stdout);
        std::putchar('\n');
    }
    return 0;
}