// cengine.cpp — exact C++ mirror of engine.py (corner-anchored exhaustive triangle-tiling search)
// Numbers: Q(sqrt D) as normalized integer triples (pn + qn*sqrt(D))/den, GMP mpz.
// Same branching rule, same prunes P1 (area), P2 (semigroup runs), P4 (corner angle).
// Results are cross-verified: FOUND tilings are dumped exactly and re-checked by engine.py's
// independent reverify(). An EXHAUSTED run is a proof of non-existence (complete branching).
//
// Build: clang++ -O2 -std=c++17 -I/opt/homebrew/include -L/opt/homebrew/lib cengine.cpp -lgmpxx -lgmp -o cengine
// Run:   ./cengine <instance> [node_cap]     instances: A B E I2 M56 M60 L105 N44A V1A V1B V1E V2B V2E

#include <gmpxx.h>
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>
#include <array>

static mpz_class QD_D = 3;

struct QD {
    mpz_class pn, qn, den;  // den>0, gcd(pn,qn,den)=1
    QD() : pn(0), qn(0), den(1) {}
    QD(long p) : pn(p), qn(0), den(1) {}
};

static QD qd_raw(mpz_class pn, mpz_class qn, mpz_class den) {
    QD o;
    if (den == 1) { o.pn = pn; o.qn = qn; o.den = 1; return o; }
    if (den < 0) { pn = -pn; qn = -qn; den = -den; }
    mpz_class g = gcd(gcd(pn, qn), den);
    if (g > 1) { pn /= g; qn /= g; den /= g; }
    o.pn = pn; o.qn = qn; o.den = den;
    return o;
}
static QD qd_frac(long num, long den) { return qd_raw(num, 0, den); }
static QD qd_sq3(long num, long den) { return qd_raw(0, num, den); }  // (num/den)*sqrt(D)

static QD operator+(const QD& a, const QD& b) {
    if (a.den == b.den) return qd_raw(a.pn + b.pn, a.qn + b.qn, a.den);
    return qd_raw(a.pn * b.den + b.pn * a.den, a.qn * b.den + b.qn * a.den, a.den * b.den);
}
static QD operator-(const QD& a, const QD& b) {
    if (a.den == b.den) return qd_raw(a.pn - b.pn, a.qn - b.qn, a.den);
    return qd_raw(a.pn * b.den - b.pn * a.den, a.qn * b.den - b.qn * a.den, a.den * b.den);
}
static QD operator-(const QD& a) { QD o; o.pn = -a.pn; o.qn = -a.qn; o.den = a.den; return o; }
static QD operator*(const QD& a, const QD& b) {
    return qd_raw(a.pn * b.pn + QD_D * a.qn * b.qn, a.pn * b.qn + a.qn * b.pn, a.den * b.den);
}
static QD operator/(const QD& a, const QD& b) {
    mpz_class pn = b.den * (a.pn * b.pn - QD_D * a.qn * b.qn);
    mpz_class qn = b.den * (a.qn * b.pn - a.pn * b.qn);
    mpz_class den = a.den * (b.pn * b.pn - QD_D * b.qn * b.qn);
    return qd_raw(pn, qn, den);
}
static int sgn(const mpz_class& x) { return mpz_sgn(x.get_mpz_t()); }
static int qsign(const QD& s) {
    int sp = sgn(s.pn), sq = sgn(s.qn);
    if (sp == 0 && sq == 0) return 0;
    if (sp >= 0 && sq >= 0) return 1;
    if (sp <= 0 && sq <= 0) return -1;
    mpz_class t = s.pn * s.pn - QD_D * s.qn * s.qn;
    int st = sgn(t);
    if (sp > 0) return st > 0 ? 1 : (st < 0 ? -1 : 0);
    return st > 0 ? -1 : (st < 0 ? 1 : 0);
}
static bool operator==(const QD& a, const QD& b) { return a.pn == b.pn && a.qn == b.qn && a.den == b.den; }
static bool operator!=(const QD& a, const QD& b) { return !(a == b); }
static bool qlt(const QD& a, const QD& b) { return qsign(a - b) < 0; }
static bool is_zero(const QD& a) { return sgn(a.pn) == 0 && sgn(a.qn) == 0; }

// exact sqrt when s is a nonneg rational square: returns true + num/den
static bool sqrt_rational(const QD& s, mpz_class& rn, mpz_class& rd) {
    if (sgn(s.qn) != 0 || sgn(s.pn) < 0) return false;
    mpz_class a = sqrt(s.pn), b = sqrt(s.den);
    if (a * a == s.pn && b * b == s.den) { rn = a; rd = b; return true; }
    return false;
}

struct Pt { QD x, y; };
static bool operator==(const Pt& a, const Pt& b) { return a.x == b.x && a.y == b.y; }
// strict total order on normalized triples (for sets/maps; NOT numeric order)
static int cmp_mpz(const mpz_class& a, const mpz_class& b) { return cmp(a, b); }
static int cmp_qd_key(const QD& a, const QD& b) {
    int c = cmp_mpz(a.pn, b.pn); if (c) return c;
    c = cmp_mpz(a.qn, b.qn); if (c) return c;
    return cmp_mpz(a.den, b.den);
}
struct PtLess {
    bool operator()(const Pt& a, const Pt& b) const {
        int c = cmp_qd_key(a.x, b.x); if (c) return c < 0;
        return cmp_qd_key(a.y, b.y) < 0;
    }
};
struct EdgeLess {
    bool operator()(const std::pair<Pt, Pt>& a, const std::pair<Pt, Pt>& b) const {
        PtLess pl;
        if (pl(a.first, b.first)) return true;
        if (pl(b.first, a.first)) return false;
        return pl(a.second, b.second);
    }
};

typedef std::vector<Pt> Poly;
typedef std::pair<Pt, Pt> Edge;

static QD cross3(const Pt& o, const Pt& a, const Pt& b) {
    return (a.x - o.x) * (b.y - o.y) - (a.y - o.y) * (b.x - o.x);
}
static Pt vsub(const Pt& a, const Pt& b) { return Pt{a.x - b.x, a.y - b.y}; }
static QD dot(const Pt& u, const Pt& v) { return u.x * v.x + u.y * v.y; }
static QD crossv(const Pt& u, const Pt& v) { return u.x * v.y - u.y * v.x; }

static bool on_segment(const Pt& p, const Pt& a, const Pt& b) {
    if (qsign(cross3(a, b, p)) != 0) return false;
    return qsign(dot(vsub(p, a), vsub(b, a))) >= 0 && qsign(dot(vsub(p, b), vsub(a, b))) >= 0;
}
static QD seg_param(const Pt& p, const Pt& a, const Pt& b) {
    Pt d = vsub(b, a);
    return dot(vsub(p, a), d) / dot(d, d);
}
static bool proper_cross(const Pt& a, const Pt& b, const Pt& c, const Pt& d) {
    int d1 = qsign(cross3(c, d, a)), d2 = qsign(cross3(c, d, b));
    int d3 = qsign(cross3(a, b, c)), d4 = qsign(cross3(a, b, d));
    return d1 * d2 < 0 && d3 * d4 < 0;
}
static void seg_intersections(const Pt& a, const Pt& b, const Pt& c, const Pt& d, std::vector<Pt>& pts) {
    pts.clear();
    int d1 = qsign(cross3(c, d, a)), d2 = qsign(cross3(c, d, b));
    int d3 = qsign(cross3(a, b, c)), d4 = qsign(cross3(a, b, d));
    if (d1 == 0 && d2 == 0) {
        if (on_segment(c, a, b)) pts.push_back(c);
        if (on_segment(d, a, b)) pts.push_back(d);
        if (on_segment(a, c, d)) pts.push_back(a);
        if (on_segment(b, c, d)) pts.push_back(b);
        return;
    }
    if (d1 * d2 <= 0 && d3 * d4 <= 0) {
        Pt r = vsub(b, a), s = vsub(d, c);
        QD denom = crossv(r, s);
        if (qsign(denom) != 0) {
            QD t = crossv(vsub(c, a), s) / denom;
            Pt p{a.x + t * r.x, a.y + t * r.y};
            if (on_segment(p, a, b) && on_segment(p, c, d)) pts.push_back(p);
        }
    }
}
// 'I' in, 'O' out, 'N' on
static char point_in_polygon(const Pt& pt, const Poly& poly) {
    size_t n = poly.size();
    for (size_t i = 0; i < n; i++) {
        if (on_segment(pt, poly[i], poly[(i + 1) % n])) return 'N';
    }
    int cnt = 0;
    for (size_t i = 0; i < n; i++) {
        const Pt& a = poly[i];
        const Pt& b = poly[(i + 1) % n];
        int s1 = qsign(a.y - pt.y), s2 = qsign(b.y - pt.y);
        if ((s1 <= 0 && s2 > 0) || (s2 <= 0 && s1 > 0)) {
            QD t = (pt.y - a.y) / (b.y - a.y);
            QD xc = a.x + t * (b.x - a.x);
            if (qsign(xc - pt.x) > 0) cnt++;
        }
    }
    return (cnt % 2 == 1) ? 'I' : 'O';
}
static QD poly_area2(const Poly& poly) {
    QD s;
    size_t n = poly.size();
    for (size_t i = 0; i < n; i++) {
        const Pt& a = poly[i];
        const Pt& b = poly[(i + 1) % n];
        s = s + (a.x * b.y - b.x * a.y);
    }
    return s;
}

// ------------------------------------------------------------------ tile & instances --------
struct Corner { QD cs, sn; long L1, M1, L2, M2; };  // two side pairs (L along, M other)
struct Tile {
    long a, b, c;
    QD area2;
    Corner corners[3];
};
static Pt rotv(const QD& cs, const QD& sn, const Pt& u) {
    return Pt{cs * u.x - sn * u.y, sn * u.x + cs * u.y};
}

// ---------------------------------------------------------------------- semigroup -----------
struct Semigroup {
    long g[3];
    std::unordered_map<long, char> memo;
    bool contains_int(long n) {
        if (n < 0) return false;
        if (n == 0) return true;
        auto it = memo.find(n);
        if (it != memo.end()) return it->second;
        bool ok = false;
        for (int i = 0; i < 3 && !ok; i++)
            if (n - g[i] >= 0) ok = contains_int(n - g[i]);
        memo[n] = ok ? 1 : 0;
        return ok;
    }
};

// ------------------------------------------------------------------------ subtraction -------
static void split_edges(std::vector<Edge>& edges) {
    size_t n = edges.size();
    std::vector<std::set<Pt, PtLess>> cut(n);
    std::vector<Pt> pts;
    for (size_t i = 0; i < n; i++) {
        const Pt &a = edges[i].first, &b = edges[i].second;
        for (size_t j = 0; j < n; j++) {
            if (i == j) continue;
            seg_intersections(a, b, edges[j].first, edges[j].second, pts);
            for (const Pt& p : pts)
                if (!(p == a) && !(p == b) && on_segment(p, a, b)) cut[i].insert(p);
        }
    }
    std::vector<Edge> out;
    for (size_t i = 0; i < n; i++) {
        const Pt &a = edges[i].first, &b = edges[i].second;
        if (cut[i].empty()) { out.push_back(edges[i]); continue; }
        std::vector<std::pair<QD, Pt>> ps;
        for (const Pt& p : cut[i]) ps.push_back({seg_param(p, a, b), p});
        std::sort(ps.begin(), ps.end(), [](const std::pair<QD, Pt>& x, const std::pair<QD, Pt>& y) {
            return qlt(x.first, y.first);
        });
        Pt prev = a;
        for (auto& pp : ps) {
            if (!(pp.second == prev)) out.push_back({prev, pp.second});
            prev = pp.second;
        }
        if (!(prev == b)) out.push_back({prev, b});
    }
    edges.swap(out);
}

static bool subtract(const Poly& poly, const Poly& tri, std::vector<Poly>& out) {
    out.clear();
    std::vector<Edge> edges;
    size_t n = poly.size();
    for (size_t i = 0; i < n; i++) edges.push_back({poly[i], poly[(i + 1) % n]});
    for (int i = 0; i < 3; i++) edges.push_back({tri[(i + 1) % 3], tri[i]});
    split_edges(edges);
    // cancel exact opposite pairs (multiset, first-appearance order)
    std::map<Edge, int, EdgeLess> cnt;
    std::vector<Edge> order;
    for (const Edge& e : edges) {
        auto it = cnt.find(e);
        if (it == cnt.end()) { cnt[e] = 1; order.push_back(e); }
        else it->second++;
    }
    for (const Edge& e : order) {
        int k = cnt[e];
        if (k == 0) continue;
        Edge rev{e.second, e.first};
        auto it = cnt.find(rev);
        int rk = (it == cnt.end()) ? 0 : it->second;
        int m = std::min(k, rk);
        if (m > 0) { cnt[e] = k - m; cnt[rev] = rk - m; }
    }
    std::vector<Edge> final_;
    for (const Edge& e : order)
        for (int i = 0; i < cnt[e]; i++) final_.push_back(e);
    if (final_.empty()) return true;
    // stitch loops: clockwise-most outgoing edge from reversed incoming direction
    std::map<Pt, std::vector<int>, PtLess> outmap;
    for (size_t i = 0; i < final_.size(); i++) outmap[final_[i].first].push_back((int)i);
    std::vector<char> used(final_.size(), 0);
    auto sector = [](int cx, int dx) {
        if (cx == 0 && dx > 0) return 0;
        if (cx > 0) return 1;
        if (cx == 0) return 2;
        return 3;
    };
    for (size_t si = 0; si < final_.size(); si++) {
        if (used[si]) continue;
        std::vector<int> loop;
        loop.push_back((int)si);
        used[si] = 1;
        int cur = (int)si;
        int guard = 0;
        while (true) {
            if (++guard > 10000) return false;  // stitch runaway
            const Edge& ce = final_[cur];
            Pt w = vsub(ce.first, ce.second);
            auto it = outmap.find(ce.second);
            if (it == outmap.end()) return false;  // open chain
            int best = -1;
            for (int ei : it->second) {
                if (used[ei] && ei != (int)si) continue;
                if (best == -1) { best = ei; continue; }
                Pt u = vsub(final_[ei].second, final_[ei].first);
                Pt v = vsub(final_[best].second, final_[best].first);
                int su = sector(qsign(crossv(w, u)), qsign(dot(w, u)));
                int sv = sector(qsign(crossv(w, v)), qsign(dot(w, v)));
                bool less;
                if (su != sv) less = su > sv;
                else less = qsign(crossv(u, v)) < 0;
                if (less) best = ei;
            }
            if (best == -1) return false;  // open chain
            if (best == (int)si) break;
            loop.push_back(best);
            used[best] = 1;
            cur = best;
        }
        Poly pts;
        for (int ei : loop) pts.push_back(final_[ei].first);
        QD a2 = poly_area2(pts);
        int s = qsign(a2);
        if (s > 0) out.push_back(pts);
        else if (s < 0) return false;  // negative loop: stitching bug
        // zero-area loops: skip (degenerate sliver)
    }
    return true;
}

// ------------------------------------------------------------------------ containment -------
static char in_tri(const Poly& tri, const Pt& p) {
    int s1 = qsign(cross3(tri[0], tri[1], p));
    int s2 = qsign(cross3(tri[1], tri[2], p));
    int s3 = qsign(cross3(tri[2], tri[0], p));
    if (s1 > 0 && s2 > 0 && s3 > 0) return 'I';
    if (s1 >= 0 && s2 >= 0 && s3 >= 0) return 'N';
    return 'O';
}
static bool containment_ok(const Poly& tri, const Poly& poly) {
    size_t n = poly.size();
    std::vector<Pt> pts;
    for (int i = 0; i < 3; i++) {
        const Pt &a = tri[i], &b = tri[(i + 1) % 3];
        for (size_t j = 0; j < n; j++)
            if (proper_cross(a, b, poly[j], poly[(j + 1) % n])) return false;
    }
    for (int i = 0; i < 3; i++) {
        const Pt &a = tri[i], &b = tri[(i + 1) % 3];
        std::vector<QD> params;
        params.push_back(QD(0));
        params.push_back(QD(1));
        for (size_t j = 0; j < n; j++) {
            seg_intersections(a, b, poly[j], poly[(j + 1) % n], pts);
            for (const Pt& p : pts) params.push_back(seg_param(p, a, b));
        }
        std::sort(params.begin(), params.end(), qlt);
        params.erase(std::unique(params.begin(), params.end(),
                                 [](const QD& x, const QD& y) { return x == y; }),
                     params.end());
        for (size_t i2 = 0; i2 + 1 < params.size(); i2++) {
            QD t = (params[i2] + params[i2 + 1]) / QD(2);
            Pt mid{a.x + (b.x - a.x) * t, a.y + (b.y - a.y) * t};
            if (point_in_polygon(mid, poly) == 'O') return false;
        }
    }
    for (const Pt& v : poly)
        if (in_tri(tri, v) == 'I') return false;
    for (size_t j = 0; j < n; j++) {
        const Pt &c = poly[j], &d = poly[(j + 1) % n];
        std::vector<QD> params;
        params.push_back(QD(0));
        params.push_back(QD(1));
        for (int i = 0; i < 3; i++) {
            seg_intersections(c, d, tri[i], tri[(i + 1) % 3], pts);
            for (const Pt& p : pts) params.push_back(seg_param(p, c, d));
        }
        std::sort(params.begin(), params.end(), qlt);
        params.erase(std::unique(params.begin(), params.end(),
                                 [](const QD& x, const QD& y) { return x == y; }),
                     params.end());
        for (size_t i2 = 0; i2 + 1 < params.size(); i2++) {
            QD t = (params[i2] + params[i2 + 1]) / QD(2);
            Pt mid{c.x + (d.x - c.x) * t, c.y + (d.y - c.y) * t};
            if (in_tri(tri, mid) == 'I') return false;
        }
    }
    return true;
}

// ------------------------------------------------------------------- P5: gamma-trap walk prune ---
// Each side of the target is partitioned into whole tile edges, so its edge multiset (#a,#b,#c) is a
// "walk".  The gamma-injection lemma (paper; BaseBetaWalks.lean) forces #c >= 1 on EVERY side, for
// every scale m: each a-edge tile and each b-edge tile puts a gamma at a junction, no gamma sits at a
// base corner (one tile, angle beta) or the apex (three tiles, all alpha), and a pi-vertex carries at
// most one gamma -- so the map (a/b-edge -> its gamma junction) is injective, giving #a+#b <= k-1.
// WALK_BASE / WALK_SIDE list the surviving walks; a partial walk is pruned as soon as it is not a
// componentwise sub-multiset of any of them.  Verified against the real 44- and 99-tilings: all six
// of their sides satisfy #c >= 1.  Absent from the instance file => prune disabled (bit-identical to
// the previous engine).
static bool WALK_PRUNE = false;
static std::vector<std::array<long, 3>> WALK_BASE, WALK_SIDE;

// ------------------------------------------------------------------------------ search ------
struct Search {
    Tile tile;
    Poly target;
    long N;
    std::string name;
    long long nodes = 0, node_cap = 0, prune_area = 0, prune_run = 0, prune_dir = 0, prune_walk = 0;
    long walk[3][3] = {{0, 0, 0}, {0, 0, 0}, {0, 0, 0}};  // [side][a|b|c]
    long maxdepth = 0;
    Semigroup semi;
    QD cosmin2;
    std::vector<Poly> found;
    bool has_found = false;
    time_t t0 = 0, last_log = 0;

    // side 0 = (target[0],target[1]) = the base; sides 1,2 = the equal sides
    bool walk_ok(int s) const {
        const std::vector<std::array<long, 3>>& allowed = (s == 0) ? WALK_BASE : WALK_SIDE;
        for (size_t i = 0; i < allowed.size(); i++)
            if (walk[s][0] <= allowed[i][0] && walk[s][1] <= allowed[i][1] &&
                walk[s][2] <= allowed[i][2])
                return true;
        return false;
    }
    // every edge of `tri` that lies inside a side of the target, tagged (side, a|b|c)
    void boundary_edges(const Poly& tri, std::vector<std::pair<int, int>>& out) const {
        out.clear();
        for (int i = 0; i < 3; i++) {
            const Pt& p = tri[i];
            const Pt& q = tri[(i + 1) % 3];
            for (int s = 0; s < 3; s++) {
                const Pt& A = target[s];
                const Pt& B = target[(s + 1) % 3];
                if (on_segment(p, A, B) && on_segment(q, A, B)) {
                    Pt d = vsub(q, p);
                    QD L2 = dot(d, d);
                    int idx = -1;
                    if (L2 == qd_frac(tile.a * tile.a, 1)) idx = 0;
                    else if (L2 == qd_frac(tile.b * tile.b, 1)) idx = 1;
                    else if (L2 == qd_frac(tile.c * tile.c, 1)) idx = 2;
                    if (idx < 0) { fprintf(stderr, "FATAL: boundary edge not a tile edge\n"); exit(5); }
                    out.push_back(std::make_pair(s, idx));
                    break;
                }
            }
        }
    }

    bool corner_ok(const Poly& poly) {
        size_t n = poly.size();
        for (size_t i = 0; i < n; i++) {
            const Pt& pv = poly[(i + n - 1) % n];
            const Pt& v = poly[i];
            const Pt& nx = poly[(i + 1) % n];
            if (qsign(cross3(pv, v, nx)) <= 0) continue;
            Pt u = vsub(pv, v), w = vsub(nx, v);
            QD uw = dot(u, w);
            if (qsign(uw) <= 0) continue;
            if (qsign(uw * uw - cosmin2 * dot(u, u) * dot(w, w)) > 0) return false;
        }
        return true;
    }
    // -1 if not a positive integer multiple
    long area_multiple(const Poly& poly) {
        QD r = poly_area2(poly) / tile.area2;
        if (sgn(r.qn) != 0 || r.den != 1 || sgn(r.pn) <= 0) return -1;
        if (!r.pn.fits_slong_p()) return -1;
        return r.pn.get_si();
    }
    bool runs_ok(const Poly& poly) {
        size_t n = poly.size();
        std::vector<int> conv(n);
        for (size_t i = 0; i < n; i++)
            conv[i] = qsign(cross3(poly[(i + n - 1) % n], poly[i], poly[(i + 1) % n]));
        for (size_t i = 0; i < n; i++) {
            if (conv[i] == 0) continue;
            size_t j = i;
            mpz_class num = 0, den = 1;  // accumulated rational length num/den
            size_t steps = 0;
            while (true) {
                size_t jn = (j + 1) % n;
                Pt seg = vsub(poly[jn], poly[j]);
                QD L2 = dot(seg, seg);
                mpz_class rn, rd;
                if (!sqrt_rational(L2, rn, rd)) return false;
                // num/den += rn/rd
                num = num * rd + rn * den;
                den = den * rd;
                mpz_class g = gcd(num, den);
                if (g > 1) { num /= g; den /= g; }
                j = jn;
                if (++steps > n) return false;
                if (conv[j] != 0) break;
            }
            if (conv[i] > 0 && conv[j] > 0) {
                if (den != 1) return false;
                if (!num.fits_slong_p()) return false;
                if (!semi.contains_int(num.get_si())) return false;
            }
        }
        return true;
    }
    void lowest_vertex(const std::vector<Poly>& polys, int& bpi, int& bvi) {
        bpi = -1; bvi = -1;
        const Pt* bv = nullptr;
        for (size_t pi = 0; pi < polys.size(); pi++) {
            for (size_t vi = 0; vi < polys[pi].size(); vi++) {
                const Pt& v = polys[pi][vi];
                if (bv == nullptr) { bv = &v; bpi = (int)pi; bvi = (int)vi; continue; }
                int dy = qsign(v.y - bv->y);
                if (dy < 0 || (dy == 0 && qsign(v.x - bv->x) < 0)) {
                    bv = &v; bpi = (int)pi; bvi = (int)vi;
                }
            }
        }
    }
    void placements(const Poly& poly, int vi, std::vector<Poly>& out) {
        out.clear();
        size_t n = poly.size();
        const Pt& v = poly[vi];
        const Pt& nxt = poly[(vi + 1) % n];
        const Pt& prv = poly[(vi + n - 1) % n];
        // unit dirs (edge lengths must be rational)
        auto unit = [](const Pt& p, const Pt& q, Pt& u) {
            Pt d = vsub(q, p);
            QD L2 = dot(d, d);
            mpz_class rn, rd;
            if (!sqrt_rational(L2, rn, rd)) {
                fprintf(stderr, "FATAL: boundary edge length not rational\n");
                exit(3);
            }
            QD L = qd_raw(rn, 0, rd);
            u = Pt{d.x / L, d.y / L};
        };
        Pt u, w;
        unit(v, nxt, u);
        unit(v, prv, w);
        for (int ci = 0; ci < 3; ci++) {
            const Corner& C = tile.corners[ci];
            Pt r = rotv(C.cs, C.sn, u);
            if (qsign(crossv(u, r)) < 0 || qsign(crossv(r, w)) < 0) continue;
            long Ls[2] = {C.L1, C.L2}, Ms[2] = {C.M1, C.M2};
            for (int k = 0; k < 2; k++) {
                QD L(Ls[k]), M(Ms[k]);
                Pt p2{v.x + u.x * L, v.y + u.y * L};
                Pt p3{v.x + r.x * M, v.y + r.y * M};
                Poly tri{v, p2, p3};
                if (qsign(poly_area2(tri)) <= 0) tri = Poly{v, p3, p2};
                out.push_back(tri);
            }
        }
    }
    void dfs(std::vector<Poly>& polys, long left, std::vector<Poly>& placed) {
        if (has_found || nodes >= node_cap) return;
        nodes++;
        long d = N - left;
        if (d > maxdepth) maxdepth = d;
        time_t now = time(nullptr);
        if (now - last_log >= 60) {
            last_log = now;
            printf("  [%s] nodes=%lld depth=%ld max=%ld pruneA=%lld pruneR=%lld pruneP4=%lld pruneP5=%lld t=%lds\n",
                   name.c_str(), nodes, d, maxdepth, prune_area, prune_run, prune_dir, prune_walk,
                   (long)(now - t0));
            fflush(stdout);
        }
        if (polys.empty()) {
            if (left == 0) { found = placed; has_found = true; }
            return;
        }
        if (left == 0) return;
        long total = 0;
        for (const Poly& p : polys) {
            long m = area_multiple(p);
            if (m < 0) { prune_area++; return; }
            total += m;
        }
        if (total != left) { prune_area++; return; }
        for (const Poly& p : polys)
            if (!runs_ok(p)) { prune_run++; return; }
        for (const Poly& p : polys)
            if (!corner_ok(p)) { prune_dir++; return; }
        int pi, vi;
        lowest_vertex(polys, pi, vi);
        Poly poly = polys[pi];
        std::vector<Poly> rest;
        for (size_t i = 0; i < polys.size(); i++)
            if ((int)i != pi) rest.push_back(polys[i]);
        std::vector<Poly> cands;
        placements(poly, vi, cands);
        std::vector<Poly> pieces;
        std::vector<std::pair<int, int>> bedges;
        for (Poly& tri : cands) {
            if (!containment_ok(tri, poly)) continue;
            if (WALK_PRUNE) {
                boundary_edges(tri, bedges);
                for (size_t k = 0; k < bedges.size(); k++) walk[bedges[k].first][bedges[k].second]++;
                bool bad = false;
                for (size_t k = 0; k < bedges.size(); k++)
                    if (!walk_ok(bedges[k].first)) { bad = true; break; }
                if (bad) {
                    for (size_t k = 0; k < bedges.size(); k++) walk[bedges[k].first][bedges[k].second]--;
                    prune_walk++;
                    continue;
                }
            }
            if (!subtract(poly, tri, pieces)) {
                fprintf(stderr, "FATAL: subtract surgery degenerate\n");
                exit(4);
            }
            std::vector<Poly> next = rest;
            for (Poly& pc : pieces) next.push_back(pc);
            placed.push_back(tri);
            dfs(next, left - 1, placed);
            placed.pop_back();
            if (WALK_PRUNE)
                for (size_t k = 0; k < bedges.size(); k++) walk[bedges[k].first][bedges[k].second]--;
            if (has_found) return;
        }
    }
    const char* run() {
        t0 = last_log = time(nullptr);
        // root checks
        QD ta2 = poly_area2(target);
        if (qsign(ta2) <= 0) { fprintf(stderr, "target not CCW\n"); exit(2); }
        QD r = ta2 / tile.area2;
        if (sgn(r.qn) != 0 || r.den != 1 || r.pn != N) {
            fprintf(stderr, "root area mismatch\n");
            exit(2);
        }
        // P4 constant
        long s[3] = {tile.a, tile.b, tile.c};
        std::sort(s, s + 3);
        // cos of smallest angle (opposite smallest side s[0]) = (s1^2+s2^2-s0^2)/(2 s1 s2)
        mpz_class num = (mpz_class)s[1] * s[1] + (mpz_class)s[2] * s[2] - (mpz_class)s[0] * s[0];
        mpz_class den = 2 * (mpz_class)s[1] * s[2];
        cosmin2 = qd_raw(num * num, 0, den * den);
        semi.g[0] = tile.a; semi.g[1] = tile.b; semi.g[2] = tile.c;
        std::vector<Poly> polys{target};
        std::vector<Poly> placed;
        dfs(polys, N, placed);
        if (has_found) return "FOUND_TILING";
        if (nodes >= node_cap) return "INCONCLUSIVE";
        return "EXHAUSTED_NO_TILING";
    }
};

// ---------------------------------------------------------------------------- instances -----
static Tile tile_120(long a, long b, long c) {
    // 120-degree tile in Q(sqrt3): cosA=(2b+a)/(2c), sinA=a/(2c) sqrt3, etc.
    Tile t;
    t.a = a; t.b = b; t.c = c;
    t.area2 = qd_sq3(a * b, 2);
    t.corners[0] = {qd_frac(2 * b + a, 2 * c), qd_sq3(a, 2 * c), b, c, c, b};
    t.corners[1] = {qd_frac(2 * a + b, 2 * c), qd_sq3(b, 2 * c), a, c, c, a};
    t.corners[2] = {qd_frac(-1, 2), qd_sq3(1, 2), a, b, b, a};
    return t;
}
// FILE:<path> — read an exact instance emitted by dump_inst.py (python's run_all.make_instance).
// Guarantees cengine and engine.py branch on bit-identical instance data.
static bool make_instance_file(const std::string& path, Tile& tile, Poly& target, long& N) {
    FILE* fp = fopen(path.c_str(), "r");
    if (!fp) { fprintf(stderr, "cannot open %s\n", path.c_str()); return false; }
    auto rd_mpz = [&](mpz_class& z) {
        char buf[4096];
        if (fscanf(fp, "%4095s", buf) != 1) { fprintf(stderr, "instance file truncated\n"); exit(1); }
        z = mpz_class(buf);
    };
    auto rd_qd = [&]() {
        mpz_class p, q, d; rd_mpz(p); rd_mpz(q); rd_mpz(d);
        return qd_raw(p, q, d);
    };
    auto rd_long = [&]() { mpz_class z; rd_mpz(z); return z.get_si(); };
    rd_mpz(QD_D);
    tile.a = rd_long(); tile.b = rd_long(); tile.c = rd_long();
    long adj[3][2] = {{tile.b, tile.c}, {tile.a, tile.c}, {tile.a, tile.b}};
    for (int i = 0; i < 3; i++) {
        QD cs = rd_qd(), sn = rd_qd();
        tile.corners[i] = {cs, sn, adj[i][0], adj[i][1], adj[i][1], adj[i][0]};
    }
    tile.area2 = rd_qd();
    N = rd_long();
    target.clear();
    for (int i = 0; i < 3; i++) { QD x = rd_qd(), y = rd_qd(); target.push_back(Pt{x, y}); }
    // optional trailing "WALKS <nb> <nb triples> <ns> <ns triples>" section (P5)
    char tok[4096];
    if (fscanf(fp, "%4095s", tok) == 1 && std::string(tok) == "WALKS") {
        long nb = rd_long();
        for (long i = 0; i < nb; i++) {
            long p = rd_long(), q = rd_long(), r = rd_long();
            WALK_BASE.push_back({p, q, r});
        }
        long ns = rd_long();
        for (long i = 0; i < ns; i++) {
            long p = rd_long(), q = rd_long(), r = rd_long();
            WALK_SIDE.push_back({p, q, r});
        }
        WALK_PRUNE = true;
        fprintf(stderr, "P5 walk prune ON: %ld base walks, %ld side walks\n", nb, ns);
    }
    fclose(fp);
    return true;
}

static bool make_instance(const std::string& name, Tile& tile, Poly& target, long& N) {
    auto P = [](QD x, QD y) { return Pt{x, y}; };
    if (name.rfind("FILE:", 0) == 0) return make_instance_file(name.substr(5), tile, target, N);
    if (name == "A" || name == "V1A") {
        QD_D = 3; tile = tile_120(7, 8, 13); N = 14;
        target = {P(QD(0), QD(0)), P(QD(28), QD(0)), P(QD(14), qd_sq3(14, 1))};
        if (name == "V1A") {  // reptile: tile scaled by 2 -> N=4
            N = 4;
            QD b2 = QD(2 * 8);
            target = {P(QD(0), QD(0)), P(QD(26), QD(0)),
                      P(tile.corners[0].cs * b2, tile.corners[0].sn * b2)};
        }
        return true;
    }
    if (name == "B" || name == "V1B" || name == "V2B") {
        QD_D = 3; tile = tile_120(3, 5, 7); N = 15;
        target = {P(QD(0), QD(0)), P(QD(15), QD(0)), P(qd_frac(15, 2), qd_sq3(15, 2))};
        if (name == "V1B") {
            N = 4;
            QD b2 = QD(10);
            target = {P(QD(0), QD(0)), P(QD(14), QD(0)),
                      P(tile.corners[0].cs * b2, tile.corners[0].sn * b2)};
        }
        if (name == "V2B") {
            N = 1;
            QD b1 = QD(5);
            target = {P(QD(0), QD(0)), P(QD(7), QD(0)),
                      P(tile.corners[0].cs * b1, tile.corners[0].sn * b1)};
        }
        return true;
    }
    if (name == "E" || name == "V1E" || name == "V2E") {
        QD_D = 7;
        Tile t;
        t.a = 4; t.b = 15; t.c = 16;
        t.area2 = qd_sq3(45, 2);  // (0, 45/2) * sqrt7
        t.corners[0] = {qd_frac(31, 32), qd_sq3(3, 32), 15, 16, 16, 15};
        t.corners[1] = {qd_frac(47, 128), qd_sq3(45, 128), 4, 16, 16, 4};
        t.corners[2] = {qd_frac(-1, 8), qd_sq3(3, 8), 4, 15, 15, 4};
        tile = t; N = 15;
        target = {P(QD(0), QD(0)), P(QD(15), QD(0)), P(qd_frac(15, 2), qd_sq3(45, 2))};
        if (name == "V1E") {
            N = 4;
            QD b2 = QD(30);
            target = {P(QD(0), QD(0)), P(QD(32), QD(0)),
                      P(t.corners[0].cs * b2, t.corners[0].sn * b2)};
        }
        if (name == "V2E") {
            N = 1;
            QD b1 = QD(15);
            target = {P(QD(0), QD(0)), P(QD(16), QD(0)),
                      P(t.corners[0].cs * b1, t.corners[0].sn * b1)};
        }
        return true;
    }
    if (name == "I2") {
        QD_D = 6;
        Tile t;
        t.a = 10; t.b = 21; t.c = 25;
        t.area2 = qd_sq3(84, 1);
        t.corners[0] = {qd_frac(23, 25), qd_sq3(4, 25), 21, 25, 25, 21};
        t.corners[1] = {qd_frac(71, 125), qd_sq3(42, 125), 10, 25, 25, 10};
        t.corners[2] = {qd_frac(-1, 5), qd_sq3(2, 5), 10, 21, 21, 10};
        tile = t; N = 21;
        target = {P(QD(0), QD(0)), P(QD(42), QD(0)), P(QD(21), qd_sq3(42, 1))};
        return true;
    }
    if (name == "M56") {
        QD_D = 3; tile = tile_120(8, 7, 13); N = 56;
        target = {P(QD(0), QD(0)), P(QD(56), QD(0)), P(QD(28), qd_sq3(28, 1))};
        return true;
    }
    if (name == "M60") {
        QD_D = 3; tile = tile_120(5, 3, 7); N = 60;
        target = {P(QD(0), QD(0)), P(QD(30), QD(0)), P(QD(15), qd_sq3(15, 1))};
        return true;
    }
    if (name == "L105") {
        QD_D = 3; tile = tile_120(8, 7, 13); N = 105;
        target = {P(QD(0), QD(0)), P(QD(105), QD(0)), P(QD(28), qd_sq3(28, 1))};
        return true;
    }
    if (name == "N76") {
        // N=76 iso-(alpha+beta) (Thm 17, M=2): tile (90,19,100), target (380,380,342), D=319
        QD_D = 319;
        Tile t;
        t.a = 90; t.b = 19; t.c = 100;
        t.area2 = qd_sq3(171, 2);
        t.corners[0] = {qd_frac(119, 200), qd_sq3(9, 200), 19, 100, 100, 19};
        t.corners[1] = {qd_frac(1971, 2000), qd_sq3(19, 2000), 90, 100, 100, 90};
        t.corners[2] = {qd_frac(-9, 20), qd_sq3(1, 20), 90, 19, 19, 90};
        tile = t; N = 76;
        target = {P(QD(0), QD(0)), P(QD(342), QD(0)), P(QD(171), qd_sq3(19, 1))};
        return true;
    }
    if (name == "G63") {
        // N=63 gamma=2alpha instance: tile (9,7,12) angles (alpha,beta,2alpha), target (63,63,84)
        QD_D = 5;
        Tile t;
        t.a = 9; t.b = 7; t.c = 12;
        t.area2 = qd_sq3(28, 1);
        t.corners[0] = {qd_frac(2, 3), qd_sq3(1, 3), 7, 12, 12, 7};
        t.corners[1] = {qd_frac(22, 27), qd_sq3(7, 27), 9, 12, 12, 9};
        t.corners[2] = {qd_frac(-1, 9), qd_sq3(4, 9), 9, 7, 7, 9};
        tile = t; N = 63;
        target = {P(QD(0), QD(0)), P(QD(84), QD(0)), P(QD(42), qd_sq3(21, 1))};
        return true;
    }
    if (name == "T77") {
        // N=77: tile (2,3,4) tiling the (2a,a,2b) triangle (28,16,33). Beeson four-component
        // (second tiling eq (M,s)=(5,1/2)). If FOUND -> unconditional realizability certificate.
        QD_D = 15;
        Tile t;
        t.a = 2; t.b = 3; t.c = 4;
        t.area2 = qd_sq3(3, 2);
        t.corners[0] = {qd_frac(7, 8), qd_sq3(1, 8), 3, 4, 4, 3};
        t.corners[1] = {qd_frac(11, 16), qd_sq3(3, 16), 2, 4, 4, 2};
        t.corners[2] = {qd_frac(-1, 4), qd_sq3(1, 4), 2, 3, 3, 2};
        tile = t; N = 77;
        target = {P(QD(0), QD(0)), P(QD(33), QD(0)), P(qd_frac(17, 2), qd_sq3(7, 2))};
        return true;
    }
    if (name == "T28") {
        // N=28: tile (2,3,4) tiling the (2a,b,a+b) triangle (14,12,16). Beeson triquadratic
        // (tiling eq (K,M)=(4,2)). Smallest triquadratic. FOUND -> unconditional certificate.
        QD_D = 15;
        Tile t;
        t.a = 2; t.b = 3; t.c = 4;
        t.area2 = qd_sq3(3, 2);
        t.corners[0] = {qd_frac(7, 8), qd_sq3(1, 8), 3, 4, 4, 3};
        t.corners[1] = {qd_frac(11, 16), qd_sq3(3, 16), 2, 4, 4, 2};
        t.corners[2] = {qd_frac(-1, 4), qd_sq3(1, 4), 2, 3, 3, 2};
        tile = t; N = 28;
        target = {P(QD(0), QD(0)), P(QD(16), QD(0)), P(qd_frac(51, 8), qd_sq3(21, 8))};
        return true;
    }
    if (name == "N44B") {
        // N=44 iso-beta (Beeson III Thm 14, M=6, s=1/2): tile (2,3,4), target (16,16,22), D=15
        QD_D = 15;
        Tile t;
        t.a = 2; t.b = 3; t.c = 4;
        t.area2 = qd_sq3(3, 2);
        t.corners[0] = {qd_frac(7, 8), qd_sq3(1, 8), 3, 4, 4, 3};
        t.corners[1] = {qd_frac(11, 16), qd_sq3(3, 16), 2, 4, 4, 2};
        t.corners[2] = {qd_frac(-1, 4), qd_sq3(1, 4), 2, 3, 3, 2};
        tile = t; N = 44;
        target = {P(QD(0), QD(0)), P(QD(22), QD(0)), P(QD(11), qd_sq3(3, 1))};
        return true;
    }
    if (name == "N44A") {
        QD_D = 119;
        Tile t;
        t.a = 30; t.b = 11; t.c = 36;
        t.area2 = qd_sq3(55, 2);
        t.corners[0] = {qd_frac(47, 72), qd_sq3(5, 72), 11, 36, 36, 11};
        t.corners[1] = {qd_frac(415, 432), qd_sq3(11, 432), 30, 36, 36, 30};
        t.corners[2] = {qd_frac(-5, 12), qd_sq3(1, 12), 30, 11, 11, 30};
        tile = t; N = 44;
        target = {P(QD(0), QD(0)), P(QD(110), QD(0)), P(QD(55), qd_sq3(11, 1))};
        return true;
    }
    return false;
}

static void dump_qd(FILE* f, const QD& x) {
    gmp_fprintf(f, "%Zd %Zd %Zd", x.pn.get_mpz_t(), x.qn.get_mpz_t(), x.den.get_mpz_t());
}

int main(int argc, char** argv) {
    if (argc < 2) { fprintf(stderr, "usage: cengine <instance> [node_cap]\n"); return 1; }
    std::string name = argv[1];
    long long cap = (argc > 2) ? atoll(argv[2]) : 2000000000LL;
    Search S;
    if (!make_instance(name, S.tile, S.target, S.N)) {
        fprintf(stderr, "unknown instance %s\n", name.c_str());
        return 1;
    }
    S.name = name;
    S.node_cap = cap;
    gmp_printf("instance %s: N=%ld D=%Zd cap=%lld\n", name.c_str(), S.N, QD_D.get_mpz_t(), cap);
    fflush(stdout);
    const char* r = S.run();
    printf("RESULT %s nodes=%lld maxdepth=%ld pruneA=%lld pruneR=%lld pruneP4=%lld pruneP5=%lld\n", r, S.nodes,
           S.maxdepth, S.prune_area, S.prune_run, S.prune_dir, S.prune_walk);
    if (S.has_found) {
        std::string fn = "tiling_" + name + ".txt";
        FILE* f = fopen(fn.c_str(), "w");
        gmp_fprintf(f, "%s %ld %Zd\n", name.c_str(), S.N, QD_D.get_mpz_t());
        for (const Poly& t : S.found) {
            for (const Pt& p : t) {
                dump_qd(f, p.x); fprintf(f, "  ");
                dump_qd(f, p.y); fprintf(f, "  ");
            }
            fprintf(f, "\n");
        }
        fclose(f);
        printf("tiling written to %s (verify with python3 reverify_c.py %s)\n", fn.c_str(), fn.c_str());
    }
    return 0;
}
