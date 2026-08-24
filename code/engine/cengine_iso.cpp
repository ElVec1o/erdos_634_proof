// cengine_iso.cpp — exact C++ mirror of engine.py (corner-anchored exhaustive triangle-tiling
// search).  Numbers: Q(sqrt D) as normalized integer triples (pn + qn*sqrt(D))/den, stored in
// __int128 when they fit and in GMP mpz when they do not; every fast-path operation is
// overflow-checked and falls back to GMP, so the arithmetic is exact either way.
// Same branching rule, same prunes P1 (area), P2 (semigroup runs), P4 (corner angle),
// P5 (walk / gamma-trap, opt-in via the instance file).
// Results are cross-verified: FOUND tilings are dumped exactly and re-checked by engine.py's
// independent reverify(). An EXHAUSTED run is a proof of non-existence (complete branching).
//
// Build: g++ -O2 -std=c++17 -I$(brew --prefix gmp)/include -L$(brew --prefix gmp)/lib \
//            -o cengine cengine_iso.cpp -lgmpxx -lgmp
// Run:   ./cengine <instance> [node_cap] [checkpoint_file]
//          instances: FILE:<path>, or the built-ins A B E I2 M56 M60 L105 N44A V1A V1B V1E V2B V2E
//        A checkpoint file makes the run resumable: the DFS frontier is written atomically every
//        CENGINE_CKPT_SECS (default 300) and replayed on restart; the resumed run ends on the same
//        node count as an uninterrupted one.  Progress lines carry an ETA.
//        CENGINE_LOG_SECS (default 60) sets the progress interval.
//
// Validation: build with -DQD_CROSSCHECK to recompute every fast-path result in GMP and abort on
// any disagreement.  That build is slow and is meant for validation runs only.

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
#include <memory>
#include <atomic>
#include <thread>
#include <mutex>
#include <ctime>
#include <climits>
#include <cstdint>
#include <cmath>

// ==============================================================================================
// Exact Q(sqrt D) arithmetic, dual representation.
//
// A value is a normalized triple (pn + qn*sqrt(D))/den with den > 0 and gcd(pn,qn,den) = 1.
// It is stored SMALL (three __int128) whenever all three components fit in __int128, and BIG
// (three mpz_class, heap, shared) otherwise.  The representation is CANONICAL: a value is BIG
// only if it genuinely does not fit.  That matters for more than tidiness -- cmp_qd_key induces
// the iteration order of the std::set / std::map used by the boundary surgery, so the induced
// order has to be bit-identical to the all-GMP engine or the search would explore in a different
// order and node counts would differ.
//
// Every fast-path operation is overflow-checked.  A single failed check discards the fast result
// and redoes the whole operation in GMP, so the arithmetic is exact either way; the fast path is
// an optimization, never a semantic change.
//
// Measured on the N=47 instance (268,153,160 normalizations of the triple):
//     > 63 bits  10.834 %      > 127 bits  0.0076 %      > 191 bits  0 %   (max 148)
// so int64 is not viable, plain __int128 is not sound, and __int128 with a checked GMP fallback
// takes the slow path on fewer than 1 value in 13,000.
//
// Build with -DQD_CROSSCHECK to recompute every fast-path result in GMP and abort on any
// disagreement.  That build is slow and is meant for validation runs only.
// ==============================================================================================

typedef __int128 i128;
typedef unsigned __int128 u128;
static const i128 I128_MIN = (i128)1 << 127;

static mpz_class QD_D = 3;   // the radicand; set per instance
static i128 QD_Di = 3;       // its __int128 image
static bool QD_Dsmall = true;

static inline bool mpz_fits_i128(const mpz_class& z) {
    return mpz_sizeinbase(z.get_mpz_t(), 2) <= 127;
}
static inline i128 mpz_to_i128(const mpz_class& z) {   // caller guarantees mpz_fits_i128(z)
    mpz_class a = abs(z);
    mpz_class hiz = a >> 64;
    u128 h = (u128)(unsigned long long)mpz_get_ui(hiz.get_mpz_t());
    mpz_class loz = a - (hiz << 64);
    u128 l = (u128)(unsigned long long)mpz_get_ui(loz.get_mpz_t());
    i128 v = (i128)((h << 64) | l);
    return mpz_sgn(z.get_mpz_t()) < 0 ? -v : v;
}
static inline mpz_class i128_to_mpz(i128 v) {
    bool neg = v < 0;
    u128 u = neg ? (u128)0 - (u128)v : (u128)v;
    mpz_class hi = (unsigned long)(unsigned long long)(u >> 64);
    mpz_class lo = (unsigned long)(unsigned long long)(u & (u128)0xFFFFFFFFFFFFFFFFULL);
    mpz_class r = (hi << 64) + lo;
    if (neg) r = -r;
    return r;
}
// Must be called after QD_D is assigned, before any arithmetic that uses it.
static inline void qd_sync_D() {
    QD_Dsmall = mpz_fits_i128(QD_D);
    QD_Di = QD_Dsmall ? mpz_to_i128(QD_D) : 0;
}

// 128-bit division and __builtin_*_overflow on __int128 are compiler-rt libcalls
// (__udivmodti4, __umodti3, __muloti4).  Profiling the first cut of this port put ~48% of runtime
// in 128-bit software division and ~7% in the checked multiply, so both are routed around here:
// a 64x64 product always fits in 127 bits and needs no check at all, and the gcd uses hardware
// 64-bit division when it can and a division-free binary gcd when it cannot.
static inline bool fits64(i128 x) { return x >= (i128)INT64_MIN && x <= (i128)INT64_MAX; }

static inline bool cmul(i128 a, i128 b, i128& r) {
    if (fits64(a) && fits64(b)) {           // |a|,|b| < 2^63 => |ab| < 2^126, always representable
        r = (i128)(long long)a * (i128)(long long)b;
        return true;
    }
    return !__builtin_mul_overflow(a, b, &r);
}
static inline bool cadd(i128 a, i128 b, i128& r) { return !__builtin_add_overflow(a, b, &r); }
static inline bool csub(i128 a, i128 b, i128& r) { return !__builtin_sub_overflow(a, b, &r); }

static inline i128 i128_gcd(i128 a, i128 b) {   // both != I128_MIN
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    if (a == 0) return b;
    if (b == 0) return a;
    if (a <= (i128)UINT64_MAX && b <= (i128)UINT64_MAX) {       // binary gcd, 64-bit, no divide
        unsigned long long x = (unsigned long long)a, y = (unsigned long long)b;
        int sh = __builtin_ctzll(x | y);
        x >>= __builtin_ctzll(x);
        do {
            y >>= __builtin_ctzll(y);
            if (x > y) { unsigned long long t = x; x = y; y = t; }
            y -= x;
        } while (y);
        return (i128)(x << sh);
    }
    u128 u = (u128)a, v = (u128)b;                              // binary gcd, no division
    int sh = 0;
    while (((u | v) & 1) == 0) { u >>= 1; v >>= 1; ++sh; }
    while ((u & 1) == 0) u >>= 1;
    do {
        while ((v & 1) == 0) v >>= 1;
        if (u > v) { u128 t = u; u = v; v = t; }
        v -= u;
    } while (v != 0);
    return (i128)(u << sh);
}

static inline i128 i128_divexact(i128 a, i128 g) {   // g > 0 and g | a
    if (fits64(a) && fits64(g)) return (i128)((long long)a / (long long)g);
    return a / g;
}


struct BigQD { mpz_class pn, qn, den; };

struct QD {
    i128 p, q, d;                      // valid iff !B
    std::shared_ptr<const BigQD> B;    // null <=> SMALL
    QD() : p(0), q(0), d(1) {}
    QD(long v) : p(v), q(0), d(1) {}
};

static inline void qd_mpz(const QD& a, mpz_class& p, mpz_class& q, mpz_class& d) {
    if (a.B) { p = a.B->pn; q = a.B->qn; d = a.B->den; }
    else { p = i128_to_mpz(a.p); q = i128_to_mpz(a.q); d = i128_to_mpz(a.d); }
}
static inline int qd_sgn_p(const QD& a) {
    if (a.B) return mpz_sgn(a.B->pn.get_mpz_t());
    return a.p > 0 ? 1 : (a.p < 0 ? -1 : 0);
}
static inline int qd_sgn_q(const QD& a) {
    if (a.B) return mpz_sgn(a.B->qn.get_mpz_t());
    return a.q > 0 ? 1 : (a.q < 0 ? -1 : 0);
}

// The reference normalization, identical to the all-GMP engine's qd_raw, then demoted if it fits.
static QD qd_raw(mpz_class pn, mpz_class qn, mpz_class den) {
    if (den != 1) {
        if (den < 0) { pn = -pn; qn = -qn; den = -den; }
        mpz_class g = gcd(gcd(pn, qn), den);
        if (g > 1) { pn /= g; qn /= g; den /= g; }
    }
    QD o;
    if (mpz_fits_i128(pn) && mpz_fits_i128(qn) && mpz_fits_i128(den)) {
        o.p = mpz_to_i128(pn); o.q = mpz_to_i128(qn); o.d = mpz_to_i128(den);
        return o;
    }
    o.B = std::make_shared<const BigQD>(BigQD{pn, qn, den});
    return o;
}

#ifdef QD_CROSSCHECK
static long long QD_CC_COUNT = 0, QD_CC_SLOW = 0;
static void qd_cc(const QD& got, const mpz_class& pn, const mpz_class& qn, const mpz_class& den,
                  const char* op) {
    QD_CC_COUNT++;
    QD ref = qd_raw(pn, qn, den);
    mpz_class gp, gq, gd, rp, rq, rd;
    qd_mpz(got, gp, gq, gd);
    qd_mpz(ref, rp, rq, rd);
    if (gp != rp || gq != rq || gd != rd) {
        gmp_fprintf(stderr, "QD CROSSCHECK FAIL in %s: got (%Zd,%Zd,%Zd) want (%Zd,%Zd,%Zd)\n",
                    op, gp.get_mpz_t(), gq.get_mpz_t(), gd.get_mpz_t(),
                    rp.get_mpz_t(), rq.get_mpz_t(), rd.get_mpz_t());
        abort();
    }
}
#define QD_CC(got, pn, qn, den, op) qd_cc(got, pn, qn, den, op)
#define QD_CC_SLOWHIT() (QD_CC_SLOW++)
#else
#define QD_CC(got, pn, qn, den, op) ((void)0)
#define QD_CC_SLOWHIT() ((void)0)
#endif


// Fast normalization; falls back to the GMP path on the (impossible in practice) I128_MIN case.
static inline QD qd_norm_small(i128 pn, i128 qn, i128 den) {
    QD o;
    if (den == 1) { o.p = pn; o.q = qn; o.d = 1; return o; }
    if (pn == I128_MIN || qn == I128_MIN || den == I128_MIN)
        return qd_raw(i128_to_mpz(pn), i128_to_mpz(qn), i128_to_mpz(den));
    if (den < 0) { pn = -pn; qn = -qn; den = -den; }
    i128 g = i128_gcd(pn, qn);
    if (g != 1) g = i128_gcd(g, den);           // gcd(1, den) = 1, so skip the second call
    if (g > 1) {
        pn = i128_divexact(pn, g);
        qn = i128_divexact(qn, g);
        den = i128_divexact(den, g);
    }
    o.p = pn; o.q = qn; o.d = den;
    return o;
}

static QD qd_frac(long num, long den) { return qd_raw(num, 0, den); }
static QD qd_sq3(long num, long den) { return qd_raw(0, num, den); }  // (num/den)*sqrt(D)

static QD operator+(const QD& a, const QD& b) {
    if (!a.B && !b.B) {
        i128 pn, qn, den;
        if (a.d == b.d) {
            if (cadd(a.p, b.p, pn) && cadd(a.q, b.q, qn)) {
                QD r = qd_norm_small(pn, qn, a.d);
                QD_CC(r, i128_to_mpz(a.p) + i128_to_mpz(b.p), i128_to_mpz(a.q) + i128_to_mpz(b.q),
                      i128_to_mpz(a.d), "+");
                return r;
            }
        } else {
            i128 t1, t2, t3, t4;
            if (cmul(a.p, b.d, t1) && cmul(b.p, a.d, t2) && cadd(t1, t2, pn) &&
                cmul(a.q, b.d, t3) && cmul(b.q, a.d, t4) && cadd(t3, t4, qn) &&
                cmul(a.d, b.d, den)) {
                QD r = qd_norm_small(pn, qn, den);
                QD_CC(r, i128_to_mpz(pn), i128_to_mpz(qn), i128_to_mpz(den), "+");
                return r;
            }
        }
    }
    QD_CC_SLOWHIT();
    mpz_class ap, aq, ad, bp, bq, bd;
    qd_mpz(a, ap, aq, ad); qd_mpz(b, bp, bq, bd);
    if (ad == bd) return qd_raw(ap + bp, aq + bq, ad);
    return qd_raw(ap * bd + bp * ad, aq * bd + bq * ad, ad * bd);
}

static QD operator-(const QD& a, const QD& b) {
    if (!a.B && !b.B) {
        i128 pn, qn, den;
        if (a.d == b.d) {
            if (csub(a.p, b.p, pn) && csub(a.q, b.q, qn)) {
                QD r = qd_norm_small(pn, qn, a.d);
                QD_CC(r, i128_to_mpz(a.p) - i128_to_mpz(b.p), i128_to_mpz(a.q) - i128_to_mpz(b.q),
                      i128_to_mpz(a.d), "-");
                return r;
            }
        } else {
            i128 t1, t2, t3, t4;
            if (cmul(a.p, b.d, t1) && cmul(b.p, a.d, t2) && csub(t1, t2, pn) &&
                cmul(a.q, b.d, t3) && cmul(b.q, a.d, t4) && csub(t3, t4, qn) &&
                cmul(a.d, b.d, den)) {
                QD r = qd_norm_small(pn, qn, den);
                QD_CC(r, i128_to_mpz(pn), i128_to_mpz(qn), i128_to_mpz(den), "-");
                return r;
            }
        }
    }
    QD_CC_SLOWHIT();
    mpz_class ap, aq, ad, bp, bq, bd;
    qd_mpz(a, ap, aq, ad); qd_mpz(b, bp, bq, bd);
    if (ad == bd) return qd_raw(ap - bp, aq - bq, ad);
    return qd_raw(ap * bd - bp * ad, aq * bd - bq * ad, ad * bd);
}

static QD operator-(const QD& a) {
    if (!a.B && a.p != I128_MIN && a.q != I128_MIN) {
        QD o; o.p = -a.p; o.q = -a.q; o.d = a.d; return o;
    }
    mpz_class p, q, d; qd_mpz(a, p, q, d);
    QD o;
    mpz_class np = -p, nq = -q;
    if (mpz_fits_i128(np) && mpz_fits_i128(nq) && mpz_fits_i128(d)) {
        o.p = mpz_to_i128(np); o.q = mpz_to_i128(nq); o.d = mpz_to_i128(d); return o;
    }
    o.B = std::make_shared<const BigQD>(BigQD{np, nq, d});
    return o;
}

static QD operator*(const QD& a, const QD& b) {
    if (!a.B && !b.B && QD_Dsmall) {
        i128 m1, m2, m3, pn, m4, m5, qn, den;
        if (cmul(a.p, b.p, m1) && cmul(a.q, b.q, m2) && cmul(QD_Di, m2, m3) && cadd(m1, m3, pn) &&
            cmul(a.p, b.q, m4) && cmul(a.q, b.p, m5) && cadd(m4, m5, qn) &&
            cmul(a.d, b.d, den)) {
            QD r = qd_norm_small(pn, qn, den);
            QD_CC(r, i128_to_mpz(pn), i128_to_mpz(qn), i128_to_mpz(den), "*");
            return r;
        }
    }
    QD_CC_SLOWHIT();
    mpz_class ap, aq, ad, bp, bq, bd;
    qd_mpz(a, ap, aq, ad); qd_mpz(b, bp, bq, bd);
    return qd_raw(ap * bp + QD_D * aq * bq, ap * bq + aq * bp, ad * bd);
}

static QD operator/(const QD& a, const QD& b) {
    if (!a.B && !b.B && QD_Dsmall) {
        i128 m1, m2, m3, s1, pn, m4, m5, s2, qn, m6, m7, m8, s3, den;
        if (cmul(a.p, b.p, m1) && cmul(a.q, b.q, m2) && cmul(QD_Di, m2, m3) && csub(m1, m3, s1) &&
            cmul(b.d, s1, pn) &&
            cmul(a.q, b.p, m4) && cmul(a.p, b.q, m5) && csub(m4, m5, s2) &&
            cmul(b.d, s2, qn) &&
            cmul(b.p, b.p, m6) && cmul(b.q, b.q, m7) && cmul(QD_Di, m7, m8) && csub(m6, m8, s3) &&
            cmul(a.d, s3, den)) {
            QD r = qd_norm_small(pn, qn, den);
            QD_CC(r, i128_to_mpz(pn), i128_to_mpz(qn), i128_to_mpz(den), "/");
            return r;
        }
    }
    QD_CC_SLOWHIT();
    mpz_class ap, aq, ad, bp, bq, bd;
    qd_mpz(a, ap, aq, ad); qd_mpz(b, bp, bq, bd);
    mpz_class pn = bd * (ap * bp - QD_D * aq * bq);
    mpz_class qn = bd * (aq * bp - ap * bq);
    mpz_class den = ad * (bp * bp - QD_D * bq * bq);
    return qd_raw(pn, qn, den);
}

static int sgn(const mpz_class& x) { return mpz_sgn(x.get_mpz_t()); }

static int qsign(const QD& s) {
    int sp = qd_sgn_p(s), sq = qd_sgn_q(s);
    if (sp == 0 && sq == 0) return 0;
    if (sp >= 0 && sq >= 0) return 1;
    if (sp <= 0 && sq <= 0) return -1;
    int st;
    if (!s.B && QD_Dsmall) {
        i128 t1, t2, t3, t;
        if (cmul(s.p, s.p, t1) && cmul(s.q, s.q, t2) && cmul(QD_Di, t2, t3) && csub(t1, t3, t)) {
            st = t > 0 ? 1 : (t < 0 ? -1 : 0);
            if (sp > 0) return st > 0 ? 1 : (st < 0 ? -1 : 0);
            return st > 0 ? -1 : (st < 0 ? 1 : 0);
        }
    }
    QD_CC_SLOWHIT();
    mpz_class p, q, d; qd_mpz(s, p, q, d);
    mpz_class t = p * p - QD_D * q * q;
    st = sgn(t);
    if (sp > 0) return st > 0 ? 1 : (st < 0 ? -1 : 0);
    return st > 0 ? -1 : (st < 0 ? 1 : 0);
}

static bool operator==(const QD& a, const QD& b) {
    if (!a.B && !b.B) return a.p == b.p && a.q == b.q && a.d == b.d;
    if (!a.B || !b.B) return false;   // canonical: one fits, the other does not
    return a.B->pn == b.B->pn && a.B->qn == b.B->qn && a.B->den == b.B->den;
}
static bool operator!=(const QD& a, const QD& b) { return !(a == b); }
static bool qlt(const QD& a, const QD& b) { return qsign(a - b) < 0; }
static bool is_zero(const QD& a) { return qd_sgn_p(a) == 0 && qd_sgn_q(a) == 0; }

// accessors used outside this block (area_multiple, the root area check, the tiling dump)
static inline bool qd_q_is_zero(const QD& a) { return qd_sgn_q(a) == 0; }
static inline bool qd_den_is_one(const QD& a) { return a.B ? (a.B->den == 1) : (a.d == 1); }
static inline bool qd_p_fits_slong(const QD& a) {
    if (a.B) return a.B->pn.fits_slong_p();
    return a.p >= (i128)LONG_MIN && a.p <= (i128)LONG_MAX;
}
static inline long qd_p_get_si(const QD& a) { return a.B ? a.B->pn.get_si() : (long)a.p; }
static inline bool qd_p_eq_long(const QD& a, long v) {
    return a.B ? (a.B->pn == v) : (a.p == (i128)v);
}

static i128 isqrt_i128(i128 n) {   // n >= 0
    if (n < 2) return n;
    i128 x = (i128)sqrtl((long double)n);
    if (x < 1) x = 1;
    for (int i = 0; i < 8; i++) {
        i128 y = (x + n / x) >> 1;
        if (y == x) break;
        x = y;
    }
    while (x > 1 && x > n / x) x--;
    while (x + 1 <= n / (x + 1)) x++;
    return x;
}

// exact sqrt when s is a nonneg rational square: returns true + num/den
static bool sqrt_rational(const QD& s, mpz_class& rn, mpz_class& rd) {
    if (!s.B) {
        if (s.q != 0 || s.p < 0) return false;
        i128 a = isqrt_i128(s.p), b = isqrt_i128(s.d), aa, bb;
        if (cmul(a, a, aa) && cmul(b, b, bb) && aa == s.p && bb == s.d) {
            rn = i128_to_mpz(a); rd = i128_to_mpz(b); return true;
        }
        return false;
    }
    if (sgn(s.B->qn) != 0 || sgn(s.B->pn) < 0) return false;
    mpz_class a = sqrt(s.B->pn), b = sqrt(s.B->den);
    if (a * a == s.B->pn && b * b == s.B->den) { rn = a; rd = b; return true; }
    return false;
}

struct Pt { QD x, y; };
static bool operator==(const Pt& a, const Pt& b) { return a.x == b.x && a.y == b.y; }
// strict total order on normalized triples (for sets/maps; NOT numeric order).
// Must agree exactly with the all-GMP engine: it drives std::set / std::map iteration order,
// which drives the order the surgery emits polygons, which drives the search order.
static inline int cmp_i128(i128 a, i128 b) { return a < b ? -1 : (a > b ? 1 : 0); }
static int cmp_qd_key(const QD& a, const QD& b) {
    if (!a.B && !b.B) {
        int c = cmp_i128(a.p, b.p); if (c) return c;
        c = cmp_i128(a.q, b.q); if (c) return c;
        return cmp_i128(a.d, b.d);
    }
    mpz_class ap, aq, ad, bp, bq, bd;
    qd_mpz(a, ap, aq, ad); qd_mpz(b, bp, bq, bd);
    int c = cmp(ap, bp); if (c) return c;
    c = cmp(aq, bq); if (c) return c;
    return cmp(ad, bd);
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
// Most-constrained-corner anchoring. OFF by default so that every certified run reproduces
// bit-identically; set CENGINE_MRV=1 to enable it for FINDING, where node identity does not matter.
static bool g_mrv = false;
static bool g_p7 = false;   // opt-in boundary-run tile-count lower bound
static int WALK_BASESIDE = 0;   // which side index of `target` is the BASE (flip permutes it)
// ------------------------------------------------------- P6: forced corner edge types (e=1) ---
// P5 prunes on edge MULTISETS.  For e = 1, m = 1 the companion additionally pins the ORDER at the
// ends of every side (Thm e1reduce): the base begins and ends with an a-edge, and each equal side
// begins and ends with a c-edge.  Both are theorems, not local geometry -- their proof needs the
// gamma-argument -- so they are genuinely new information for the search.  Encoded here in the
// orientation-independent form: an edge lying on side s and touching either corner of s must have
// the type CORNER_TYPE[s]  (0=a, 1=b, 2=c; -1 = unconstrained).
static bool CORNER_PRUNE = false;
static int CORNER_TYPE[3] = {-1, -1, -1};
static std::vector<std::array<long, 3>> WALK_BASE, WALK_SIDE;

// ------------------------------------------------------------ P7: forced edge ORDER on one side ---
// P5 prunes edge multisets, P6 pins only the two end types.  P7 pins the entire sequence on one
// side, which is what a base-word configuration (bp, cp) names.  Opt-in via a trailing BASEWORD
// section; with it absent nothing changes, so existing node counts are untouched.
// Edge lengths are integers, so a junction at prefix length L sits at squared distance L*L from the
// side's first corner -- compared exactly in QD, the same way edge types are identified.
static bool WORD_PRUNE = false;
static int WORD_SIDE = -1;
static std::vector<int> WORD_SEQ;        // types in order from target[WORD_SIDE]
static std::vector<long> WORD_PREFIX;    // prefix lengths, size = WORD_SEQ.size() + 1

// ------------------------------------------------------------------------------ search ------
// ---------------------------------------------------------------- parallel search -----------
// The tree is split at a shallow cut into independent subtree tasks (gen_frontier), each carrying
// its full materialized state, and the tasks are exhausted by a thread pool with a shared work
// queue.  Correctness rests on one identity: the coordinator counts every node strictly above the
// cut exactly once, and each worker counts its subtree (the cut node and everything below) exactly
// once, so the parallel node total equals the serial total.  That equality is the validation bar,
// checked against the serial engine on every settled instance.  Threads share only read-only data
// (tile, target, semigroup, cos bound, WALK_* config, all fixed before the search starts); every
// mutable counter and the incremental walk[][] state is per-worker.
// A task is identified by its PATH: the sequence of candidate indices from the root down to its
// node.  Paths are deterministic and order-independent, which is what lets the queue grow
// dynamically (adaptive splitting, below) while checkpointing stays exact.
struct Task {
    std::vector<Poly> polys;
    long left;
    std::vector<Poly> placed;
    long walk_snap[3][3];
    std::vector<int> path;
};
static std::string path_key(const std::vector<int>& p) {
    std::string s;
    char buf[16];
    for (size_t i = 0; i < p.size(); i++) { snprintf(buf, sizeof buf, "%d.", p[i]); s += buf; }
    return s;
}
static std::atomic<bool> g_stop{false};                 // a tiling was found, or a hard error: unwind
static std::atomic<long long> g_nodes{0};                // aggregate node count across workers
static std::atomic<int> g_done{0};                       // workers finished
// --- parallel checkpointing -----------------------------------------------------------------
// The frontier is generated deterministically (same instance + same cut depth => same task list
// in the same order), so a checkpoint need only record WHICH tasks are finished and what each
// contributed.  A task's counters are deterministic too, so redoing an in-flight task on resume
// reproduces the same numbers: the aggregate stays exact.  At most one task per thread is redone.
struct TaskDone { long long nodes, pa, pr, pd, pw; long md; };
static std::map<std::string, TaskDone> g_leafdone;       // completed LEAF tasks, keyed by path
static std::mutex g_ckmutex;
// Adaptive splitting: a task is first attempted with a node BUDGET.  If it completes, it is a leaf
// and is recorded.  If it blows the budget it is re-run in split mode, which enqueues its children
// a few levels deeper and counts only the nodes strictly above that sub-cut.  The aborted attempt's
// counters are discarded, so nothing is double counted.  Split overhead is recomputed every run and
// is therefore never checkpointed; only leaf completions are.
static std::atomic<long long> g_leafnodes{0};   // nodes inside completed leaf tasks
static size_t g_queue_cap = 4000;    // max pending tasks (memory bound)
static long long g_budget = 200000;
static int g_split_k = 4;
static std::mutex g_qmutex;                              // guards the task queue and the winner slot
static std::vector<Task> g_queue;
static size_t g_qhead = 0;
// Dispatch order.  FIFO (the default, g_lifo=false) drains the queue front-to-back, which is
// breadth-first over subtrees: every task that blows its budget enqueues g_split_k children that
// then sit unexplored, so the frontier grows faster than it drains and no finite ETA exists.
// LIFO takes the most recently enqueued task, i.e. depth-first over subtrees, so a split is worked
// off immediately.  The set of nodes explored is identical -- only the order changes -- because task
// paths are deterministic and order-independent (see the comment above Task).  So EXHAUSTED is
// unaffected; this is a scheduling change, not a search change.
//
// MEASURED on N=138 (member (3,7)), and the measurement needs a long window to be meaningful.
//     FIFO  407 leaves closed  +16.36 pending per leaf  254 leaves/h  ~4,400 nodes/s  -> diverges
//     LIFO, after a startup transient in which pending rose 11,670 -> 12,113 over ~1080s,
//           386 leaves closed  - 1.77 pending per leaf  901 leaves/h  -> DRAINS, ETA ~7h
// Two earlier readings of this run were wrong in opposite directions: -1.00 from a window with one
// closed leaf, then +3.19 taken across the transient.  Only the post-transient figure above is
// well founded.  Rule for this engine: quote a per-leaf rate only from >= ~300 leaves AND only
// after the queue has stopped growing.
// The remaining headroom is in propagation, not scheduling: at N=47 only ~13.5% of nodes die to an
// explicit prune (11098 nodes vs 1500 prunes) and the rest is raw branching.
static bool g_lifo = false;
static size_t g_dispatched = 0;                          // tasks handed to workers (both modes)
static bool g_found_any = false;
static std::vector<Poly> g_found_tiling;

struct Search {
    Tile tile;
    Poly target;
    long N;
    std::string name;
    long long nodes = 0, node_cap = 0, prune_area = 0, prune_run = 0, prune_dir = 0, prune_walk = 0;
    bool par_mode = false;               // true inside a worker: report finds to the shared slot
    long cut_depth = -1;                 // >=0 in the coordinator: enqueue children at this depth
    // --- checkpoint / resume / ETA ---------------------------------------------------------
    // The DFS frontier is fully described by the candidate index chosen at each live level, so a
    // checkpoint is just that vector of small ints plus the counters.  Resuming replays the path
    // (a few hundred deterministic placements) and continues.  Nothing else is serialized.
    std::vector<int> cur_idx, cur_n;     // index and fan-out at each live level
    std::vector<int> resume_path;
    bool resuming = false;
    std::string ckpt_file;
    time_t last_ckpt = 0;
    long ckpt_secs = 300;
    long log_secs = 60;
    long long last_reported = 0;         // par_mode: nodes already published to g_nodes
    std::vector<int> path_prefix;        // root-path of the task this worker is running
    double frac0 = 0.0;
    bool frac0_set = true;
    // fraction of the search tree strictly to the left of the current frontier
    double progress_frac() const {
        double frac = 0.0, mult = 1.0;
        for (size_t d = 0; d < cur_idx.size() && d < cur_n.size(); d++) {
            if (cur_n[d] <= 0) break;
            mult *= (double)cur_n[d];
            if (mult > 1e300) break;
            frac += (double)cur_idx[d] / mult;
        }
        return frac;
    }
    void save_ckpt() {
        if (ckpt_file.empty()) return;
        std::string tmp = ckpt_file + ".tmp";
        FILE* f = fopen(tmp.c_str(), "w");
        if (!f) return;
        fprintf(f, "CKPT1\n%s\n%ld\n", name.c_str(), N);
        gmp_fprintf(f, "%Zd\n", QD_D.get_mpz_t());
        fprintf(f, "%lld %ld %lld %lld %lld %lld\n", nodes, maxdepth, prune_area, prune_run,
                prune_dir, prune_walk);
        fprintf(f, "%zu", cur_idx.size());
        for (size_t i = 0; i < cur_idx.size(); i++) fprintf(f, " %d", cur_idx[i]);
        fprintf(f, "\n");
        fclose(f);
        rename(tmp.c_str(), ckpt_file.c_str());   // atomic: a kill mid-save cannot corrupt it
    }
    bool load_ckpt() {
        if (ckpt_file.empty()) return false;
        FILE* f = fopen(ckpt_file.c_str(), "r");
        if (!f) return false;
        char magic[64] = {0}, nm[4096] = {0}, ds[4096] = {0};
        long n_read = 0;
        if (fscanf(f, "%63s", magic) != 1 || strcmp(magic, "CKPT1") != 0) { fclose(f); return false; }
        if (fscanf(f, "%4095s %ld %4095s", nm, &n_read, ds) != 3) { fclose(f); return false; }
        mpz_class dread(ds);
        if (n_read != N || dread != QD_D) {
            fprintf(stderr, "checkpoint is for a different instance (N=%ld); ignoring\n", n_read);
            fclose(f); return false;
        }
        long long nd, pa, pr, pd, pw; long md;
        if (fscanf(f, "%lld %ld %lld %lld %lld %lld", &nd, &md, &pa, &pr, &pd, &pw) != 6) {
            fclose(f); return false;
        }
        size_t k = 0;
        if (fscanf(f, "%zu", &k) != 1) { fclose(f); return false; }
        resume_path.assign(k, 0);
        for (size_t i = 0; i < k; i++)
            if (fscanf(f, "%d", &resume_path[i]) != 1) { fclose(f); return false; }
        fclose(f);
        nodes = nd; maxdepth = md; prune_area = pa; prune_run = pr; prune_dir = pd; prune_walk = pw;
        resuming = k > 0;
        fprintf(stderr, "resuming from checkpoint: nodes=%lld depth=%zu\n", nodes, k);
        return true;
    }
    long walk[3][3] = {{0, 0, 0}, {0, 0, 0}, {0, 0, 0}};  // [side][a|b|c]
    long maxdepth = 0;
    Semigroup semi;
    QD cosmin2;
    std::vector<Poly> found;
    bool has_found = false;
    time_t t0 = 0, last_log = 0;

    // side WALK_BASESIDE = the base; the other two are the equal sides (the apex-down flip
    // permutes these, so the index is carried in the instance file rather than assumed)
    bool walk_ok(int s) const {
        const std::vector<std::array<long, 3>>& allowed = (s == WALK_BASESIDE) ? WALK_BASE : WALK_SIDE;
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
                    // P6: an edge touching either corner of this side has a forced type
                    if (CORNER_PRUNE && CORNER_TYPE[s] >= 0 &&
                        (p == A || q == A || p == B || q == B) && idx != CORNER_TYPE[s]) {
                        out.push_back(std::make_pair(-1, -1));      // signal: reject this placement
                        return;
                    }
                    // P7: the edge must occupy the slot the seeded word assigns it
                    if (WORD_PRUNE && s == WORD_SIDE) {
                        Pt dp = vsub(p, A), dq = vsub(q, A);
                        QD dp2 = dot(dp, dp), dq2 = dot(dq, dq);
                        int slot = -1;
                        for (size_t j = 0; j + 1 < WORD_PREFIX.size(); j++) {
                            QD lo = qd_frac(WORD_PREFIX[j] * WORD_PREFIX[j], 1);
                            QD hi = qd_frac(WORD_PREFIX[j + 1] * WORD_PREFIX[j + 1], 1);
                            if ((dp2 == lo && dq2 == hi) || (dq2 == lo && dp2 == hi)) {
                                slot = (int)j; break;
                            }
                        }
                        if (slot < 0 || WORD_SEQ[slot] != idx) {
                            out.push_back(std::make_pair(-1, -1));
                            return;
                        }
                    }
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
        if (!qd_q_is_zero(r) || !qd_den_is_one(r) || qd_sgn_p(r) <= 0) return -1;
        if (!qd_p_fits_slong(r)) return -1;
        return qd_p_get_si(r);
    }
    // P7 (opt-in, CENGINE_P7).  A maximal run between two convex corners must be covered by whole
    // tile edges.  Each edge is at most c long, and two distinct edges on one straight run belong
    // to distinct tiles, because a triangle has no two collinear edges.  Every such tile is among
    // the `left` still to be placed, so  left >= ceil(L / c)  for every run.  This is a lower bound
    // on tiles from the BOUNDARY, which the area test cannot see: a long thin region can satisfy
    // the area count while needing more tiles than remain.  Sound, so it removes no tilings and
    // EXHAUSTED verdicts are preserved; it does change node counts, which is why it is gated and
    // validated by verdict identity rather than node identity.
    bool run_count_ok(long L, long left_) const {
        if (tile.c <= 0) return true;
        long need = (L + tile.c - 1) / tile.c;
        return need <= left_;
    }
    bool runs_ok(const Poly& poly, long left_ = -1) {
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
                if (g_p7 && left_ >= 0 && !run_count_ok(num.get_si(), left_)) return false;
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
    // Most-constrained convex corner, the fail-first rule (Haralick & Elliott 1980).
    //
    // Correctness needs only SOME convex corner: a tile covering a convex corner must have a vertex
    // there, since covering it mid-edge would make the tile locally a half-plane, which cannot lie
    // inside a wedge of angle below pi. `lowest_vertex` takes the globally lowest vertex, which is
    // one such corner; any other is equally legal. Choosing the corner with the fewest legal
    // placements adds two things the fixed anchor cannot give:
    //   * a convex corner with NO legal placement refutes the node immediately;
    //   * a corner with exactly one placement is forced.
    // Returns false when some convex corner admits nothing, i.e. the node is dead.
    //
    // Only (pi, vi) is returned; `placements` is recomputed by the caller exactly as before, so
    // candidate indices -- and therefore checkpoint paths -- keep their meaning.
    bool mrv_vertex(const std::vector<Poly>& polys, int& bpi, int& bvi) {
        bpi = -1; bvi = -1;
        size_t best = (size_t)-1;
        std::vector<Poly> c;
        for (size_t pi = 0; pi < polys.size(); pi++) {
            const Poly& p = polys[pi];
            size_t n = p.size();
            for (size_t vi = 0; vi < n; vi++) {
                const Pt& prv = p[(vi + n - 1) % n];
                const Pt& cur = p[vi];
                const Pt& nxt = p[(vi + 1) % n];
                if (qsign(crossv(vsub(cur, prv), vsub(nxt, cur))) <= 0) continue;  // convex only
                placements(p, (int)vi, c);
                size_t k = 0;
                for (size_t i = 0; i < c.size(); i++)
                    if (containment_ok(c[i], p)) k++;
                if (k == 0) return false;          // dead corner: the whole node is refuted
                if (k < best) {
                    best = k; bpi = (int)pi; bvi = (int)vi;
                    // constrained enough to branch on; the scan itself is quadratic in the
                    // boundary size, so looking for a better corner costs more than it saves
                    if (k <= 2) return true;
                }
            }
        }
        return bpi >= 0;
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
        if (par_mode && g_stop.load(std::memory_order_relaxed)) return;
        if (!resuming) nodes++;            // replayed nodes were counted before the checkpoint
        long d = N - left;
        if (d > maxdepth) maxdepth = d;
        time_t now = time(nullptr);
        if (par_mode) {
            // workers do not print; they publish their node delta so the coordinator can report
            if (now - last_log >= 2) {
                last_log = now;
                g_nodes.fetch_add(nodes - last_reported, std::memory_order_relaxed);
                last_reported = nodes;
            }
        } else if (!resuming && now - last_log >= log_secs) {
            last_log = now;
            double fr = progress_frac();
            if (!frac0_set) { frac0 = fr; frac0_set = true; }
            double el = (double)(now - t0);
            char eta[64];
            if (fr > frac0 && el > 0) {
                double rate = (fr - frac0) / el;
                double secs = (1.0 - fr) / (rate > 0 ? rate : 1e-300);
                if (secs > 3.0e9) snprintf(eta, sizeof eta, "  ETA~ >100y");
                else snprintf(eta, sizeof eta, "  ETA~ %02ld:%02ld:%02ld", (long)(secs / 3600),
                              ((long)secs % 3600) / 60, (long)secs % 60);
            } else snprintf(eta, sizeof eta, "  ETA~ --:--:--");
            printf("  [%s] nodes=%lld depth=%ld max=%ld pruneA=%lld pruneR=%lld pruneP4=%lld pruneP5=%lld t=%lds  done=%.6f%%%s\n",
                   name.c_str(), nodes, d, maxdepth, prune_area, prune_run, prune_dir, prune_walk,
                   (long)(now - t0), 100.0 * fr, eta);
            fflush(stdout);
            if (!ckpt_file.empty() && now - last_ckpt >= ckpt_secs) { last_ckpt = now; save_ckpt(); }
        }
        if (polys.empty()) {
            if (left == 0) {
                found = placed; has_found = true;
                if (par_mode) {
                    std::lock_guard<std::mutex> lk(g_qmutex);
                    if (!g_found_any) { g_found_any = true; g_found_tiling = placed; }
                    g_stop.store(true, std::memory_order_relaxed);
                }
            }
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
            if (!runs_ok(p, left)) { prune_run++; return; }
        for (const Poly& p : polys)
            if (!corner_ok(p)) { prune_dir++; return; }
        int pi, vi;
        if (g_mrv) {
            if (!mrv_vertex(polys, pi, vi)) { prune_dir++; return; }
        } else {
            lowest_vertex(polys, pi, vi);
        }
        Poly poly = polys[pi];
        std::vector<Poly> rest;
        for (size_t i = 0; i < polys.size(); i++)
            if ((int)i != pi) rest.push_back(polys[i]);
        std::vector<Poly> cands;
        placements(poly, vi, cands);
        std::vector<Poly> pieces;
        std::vector<std::pair<int, int>> bedges;
        size_t start = 0;
        bool this_resume = false;
        if (resuming) {
            size_t depth_here = cur_idx.size();
            if (depth_here < resume_path.size()) {
                start = (size_t)resume_path[depth_here];
                this_resume = true;
            } else {
                resuming = false;
            }
        }
        cur_idx.push_back((int)start);
        cur_n.push_back((int)cands.size());
        struct PathPop {
            std::vector<int>&a; std::vector<int>&b;
            ~PathPop(){ a.pop_back(); b.pop_back(); }
        } path_pop{cur_idx, cur_n};
        for (size_t ci_ = start; ci_ < cands.size(); ci_++) {
            cur_idx.back() = (int)ci_;
            if (this_resume && ci_ > start) { this_resume = false; resuming = false; }
            Poly& tri = cands[ci_];
            if (!containment_ok(tri, poly)) continue;
            if (WALK_PRUNE) {
                boundary_edges(tri, bedges);
                bool p6reject = false;
                for (size_t k = 0; k < bedges.size(); k++)
                    if (bedges[k].first < 0) { p6reject = true; break; }
                if (p6reject) { prune_walk++; continue; }        // P6: forced corner type violated
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
            if (cut_depth >= 0 && d + 1 >= cut_depth) {
                // coordinator: hand the child subtree off as a task instead of descending.
                // The child is NOT counted here; the worker's dfs counts it on entry, exactly as
                // serial would, so the node total is preserved.
                Task t;
                t.polys = next; t.left = left - 1; t.placed = placed;
                for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++) t.walk_snap[a][b] = walk[a][b];
                t.path = path_prefix;                       // this task's node, as a root-path
                t.path.insert(t.path.end(), cur_idx.begin(), cur_idx.end());
                if (par_mode) { std::lock_guard<std::mutex> lk(g_qmutex); g_queue.push_back(std::move(t)); }
                else g_queue.push_back(std::move(t));
            } else {
                dfs(next, left - 1, placed);
            }
            placed.pop_back();
            if (WALK_PRUNE)
                for (size_t k = 0; k < bedges.size(); k++) walk[bedges[k].first][bedges[k].second]--;
            if (has_found || (par_mode && g_stop.load(std::memory_order_relaxed))) return;
        }
    }
    const char* run() {
        qd_sync_D();
        t0 = last_log = last_ckpt = time(nullptr);
        if (const char* e = getenv("CENGINE_LOG_SECS")) log_secs = atol(e);
        if (const char* e = getenv("CENGINE_CKPT_SECS")) ckpt_secs = atol(e);
        frac0 = 0.0;
        frac0_set = !load_ckpt();
        // root checks
        QD ta2 = poly_area2(target);
        if (qsign(ta2) <= 0) { fprintf(stderr, "target not CCW\n"); exit(2); }
        QD r = ta2 / tile.area2;
        if (!qd_q_is_zero(r) || !qd_den_is_one(r) || !qd_p_eq_long(r, N)) {
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

    // set up the read-only search constants (identical to the head of run())
    void root_setup() {
        qd_sync_D();
        QD ta2 = poly_area2(target);
        if (qsign(ta2) <= 0) { fprintf(stderr, "target not CCW\n"); exit(2); }
        QD r = ta2 / tile.area2;
        if (!qd_q_is_zero(r) || !qd_den_is_one(r) || !qd_p_eq_long(r, N)) {
            fprintf(stderr, "root area mismatch\n"); exit(2);
        }
        long s[3] = {tile.a, tile.b, tile.c};
        std::sort(s, s + 3);
        mpz_class num = (mpz_class)s[1] * s[1] + (mpz_class)s[2] * s[2] - (mpz_class)s[0] * s[0];
        mpz_class den = 2 * (mpz_class)s[1] * s[2];
        cosmin2 = qd_raw(num * num, 0, den * den);
        semi.g[0] = tile.a; semi.g[1] = tile.b; semi.g[2] = tile.c;
    }

    // --- parallel checkpoint: which frontier tasks are finished, and what each contributed ---
    void par_save_ckpt(int cd) const {
        if (ckpt_file.empty()) return;
        std::lock_guard<std::mutex> lk(g_ckmutex);
        std::string tmp = ckpt_file + ".tmp";
        FILE* f = fopen(tmp.c_str(), "w");
        if (!f) return;
        fprintf(f, "PCKPT2\n%ld %d\n", N, cd);
        gmp_fprintf(f, "%Zd\n", QD_D.get_mpz_t());
        fprintf(f, "%lld %d %zu\n", g_budget, g_split_k, g_leafdone.size());
        for (const auto& kv : g_leafdone) {
            const TaskDone& r = kv.second;
            fprintf(f, "%s %lld %lld %lld %lld %lld %ld\n", kv.first.c_str(), r.nodes, r.pa,
                    r.pr, r.pd, r.pw, r.md);
        }
        fclose(f);
        rename(tmp.c_str(), ckpt_file.c_str());       // atomic
    }
    long long par_load_ckpt(int cd) {
        if (ckpt_file.empty()) return 0;
        FILE* f = fopen(ckpt_file.c_str(), "r");
        if (!f) return 0;
        char magic[32] = {0}, ds[4096] = {0};
        long n_read; int cd_read; size_t nd; long long bud; int sk;
        if (fscanf(f, "%31s %ld %d %4095s %lld %d %zu", magic, &n_read, &cd_read, ds, &bud, &sk,
                   &nd) != 7 || strcmp(magic, "PCKPT2") != 0) { fclose(f); return 0; }
        mpz_class dread(ds);
        if (n_read != N || cd_read != cd || dread != QD_D || bud != g_budget || sk != g_split_k) {
            fprintf(stderr, "parallel checkpoint does not match this instance/parameters; ignoring\n");
            fclose(f); return 0;
        }
        long long tot = 0;
        char key[8192];
        for (size_t k = 0; k < nd; k++) {
            TaskDone r;
            if (fscanf(f, "%8191s %lld %lld %lld %lld %lld %ld", key, &r.nodes, &r.pa, &r.pr,
                       &r.pd, &r.pw, &r.md) != 7) break;
            g_leafdone[std::string(key)] = r; tot += r.nodes;
        }
        fclose(f);
        fprintf(stderr, "resuming parallel run: %zu leaf tasks already done (%lld nodes)\n",
                g_leafdone.size(), tot);
        return tot;
    }

    // a fresh worker sharing this search's read-only constants
    Search make_worker() const {
        Search w;
        w.tile = tile; w.target = target; w.N = N; w.name = name;
        w.semi = semi; w.cosmin2 = cosmin2;
        w.node_cap = (long long)4e18; w.par_mode = true; w.cut_depth = -1;
        w.log_secs = 1L << 60; w.ckpt_secs = 1L << 60;
        return w;
    }

    // Parallel run: split at a shallow cut, exhaust the subtrees on `threads` workers.
    // Node total equals the serial engine's exactly (coordinator counts above the cut, workers
    // count their subtrees), which is the validation bar.
    const char* run_parallel(int threads) {
        root_setup();
        const long long cap_total = (node_cap > 0 && node_cap < (long long)1e18) ? node_cap : 0;
        node_cap = (long long)4e18;      // per-worker cap off; the coordinator enforces cap_total
        // Pick a cut depth yielding MANY more tasks than threads.  Subtree sizes are wildly skewed
        // (on N=83 a shallow cut gave 150 tasks of which 147 finished in minutes and 3 held all the
        // work), so the pool needs enough fine-grained tasks for the queue to balance the load.
        // Frontier generation is single-threaded and re-runs per trial depth, so deepening is not
        // free: it must be bounded, or generation itself explores most of the tree.  Stop as soon
        // as EITHER enough tasks exist OR the generation cost exceeds a budget.
        const std::string ckpt_save = ckpt_file;   // the gen loop clears it; restore after
        size_t target_tasks = (size_t)64 * threads;
        long long gen_budget = 2000000;
        if (const char* e = getenv("CENGINE_TASKS")) target_tasks = (size_t)atol(e);
        if (const char* e = getenv("CENGINE_GENBUDGET")) gen_budget = atoll(e);
        int cd = 3;
        for (; cd <= 14; cd++) {
            nodes = prune_area = prune_run = prune_dir = prune_walk = 0; maxdepth = 0;
            has_found = false; found.clear();
            for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++) walk[a][b] = 0;
            cur_idx.clear(); cur_n.clear(); resuming = false; ckpt_file.clear();
            log_secs = 1L << 60; g_queue.clear(); g_qhead = 0;
            cut_depth = cd; par_mode = false;
            std::vector<Poly> polys{target};
            std::vector<Poly> placed;
            dfs(polys, N, placed);
            if (has_found) return "FOUND_TILING";       // whole tree fit above the cut, and won
            if (g_queue.empty()) return "EXHAUSTED_NO_TILING";  // exhausted above the cut, no tasks
            if (g_queue.size() >= target_tasks) break;
            if (nodes >= gen_budget) break;             // deepening is costing more than it buys
        }
        ckpt_file = ckpt_save;               // RESTORE: generation cleared it (this bug silently
                                             // disabled every parallel checkpoint)
        log_secs = 60;                       // restore: frontier generation had set it to "never"
        if (const char* e = getenv("CENGINE_LOG_SECS")) log_secs = atol(e);
        if (const char* e = getenv("CENGINE_CKPT_SECS")) ckpt_secs = atol(e);
        g_leafdone.clear();
        if (const char* e = getenv("CENGINE_BUDGET")) g_budget = atoll(e);
        if (const char* e = getenv("CENGINE_SPLITK")) g_split_k = atoi(e);
        if (const char* e = getenv("CENGINE_QCAP")) g_queue_cap = (size_t)atol(e);
        if (const char* e = getenv("CENGINE_LIFO")) g_lifo = (atoi(e) != 0);
        long long done_before = par_load_ckpt(cd);
        printf("  parallel: cut depth %d, %zu subtree tasks, %d threads\n",
               cd, g_queue.size(), threads);
        fflush(stdout);
        cut_depth = -1;                  // coordinator counters below are frozen (above-cut share)
        long long co_nodes = nodes, co_pa = prune_area, co_pr = prune_run,
                  co_pd = prune_dir, co_pw = prune_walk, co_md = maxdepth;

        std::vector<Search> workers;
        workers.reserve(threads);
        for (int i = 0; i < threads; i++) workers.push_back(make_worker());
        std::vector<std::thread> pool;
        for (int i = 0; i < threads; i++) {
            Search* w = &workers[i];
            pool.emplace_back([w]() {
                std::vector<Poly> pl;
                while (true) {
                    Task t;
                    {
                        std::lock_guard<std::mutex> lk(g_qmutex);
                        if (g_stop.load(std::memory_order_relaxed)) break;
                        // skip tasks already completed as leaves in a previous run
                        if (g_lifo) {
                            while (!g_queue.empty() &&
                                   g_leafdone.count(path_key(g_queue.back().path))) g_queue.pop_back();
                            if (g_queue.empty()) break;
                            t = std::move(g_queue.back());
                            g_queue.pop_back();
                        } else {
                            while (g_qhead < g_queue.size() &&
                                   g_leafdone.count(path_key(g_queue[g_qhead].path))) g_qhead++;
                            if (g_qhead >= g_queue.size()) break;
                            t = std::move(g_queue[g_qhead++]);
                        }
                        g_dispatched++;
                    }
                    std::string key = path_key(t.path);
                    long long n0 = w->nodes, a0 = w->prune_area, r0 = w->prune_run,
                              d0 = w->prune_dir, k0 = w->prune_walk;
                    long md0 = w->maxdepth;
                    // --- attempt 1: run the whole subtree, bounded by the budget ---
                    w->has_found = false;
                    w->path_prefix = t.path;
                    w->cut_depth = -1;
                    w->node_cap = w->nodes + g_budget;
                    for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++)
                        w->walk[a][b] = t.walk_snap[a][b];
                    {
                        std::vector<Poly> pp = t.polys, pl = t.placed;
                        w->dfs(pp, t.left, pl);
                    }
                    if (g_stop.load(std::memory_order_relaxed)) break;
                    if (w->nodes < w->node_cap) {                 // completed within budget: a LEAF
                        {
                            std::lock_guard<std::mutex> lk(g_ckmutex);
                            g_leafdone[key] = TaskDone{w->nodes - n0, w->prune_area - a0,
                                                       w->prune_run - r0, w->prune_dir - d0,
                                                       w->prune_walk - k0, w->maxdepth};
                        }
                        // restore, so a worker's own totals hold ONLY split overhead; leaves are
                        // aggregated from g_leafdone (which also carries earlier runs' leaves)
                        g_leafnodes.fetch_add(w->nodes - n0, std::memory_order_relaxed);
                        w->nodes = n0; w->prune_area = a0; w->prune_run = r0;
                        w->prune_dir = d0; w->prune_walk = k0; w->maxdepth = md0;
                        w->last_reported = n0;      // keep the split-overhead delta monotone
                        continue;
                    }
                    // --- budget blown ---
                    // Splitting stores a full materialized state per task, so an unbounded queue
                    // is a memory leak in disguise (a run with ~3800 pending tasks drove the
                    // machine into swap and was killed).  Past a cap, stop splitting and just run
                    // the task to completion: slower to balance, but bounded.
                    size_t pending;
                    { std::lock_guard<std::mutex> lk(g_qmutex);
                      pending = g_lifo ? g_queue.size() : (g_queue.size() - g_qhead); }
                    if (pending >= g_queue_cap) {
                        w->nodes = n0; w->prune_area = a0; w->prune_run = r0;
                        w->prune_dir = d0; w->prune_walk = k0; w->maxdepth = md0;
                        w->last_reported = n0;
                        w->has_found = false;
                        w->node_cap = (long long)4e18;      // no budget: finish it
                        w->cut_depth = -1;
                        for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++)
                            w->walk[a][b] = t.walk_snap[a][b];
                        std::vector<Poly> pp = t.polys, pl = t.placed;
                        w->dfs(pp, t.left, pl);
                        if (!g_stop.load(std::memory_order_relaxed)) {
                            std::lock_guard<std::mutex> lk(g_ckmutex);
                            g_leafdone[key] = TaskDone{w->nodes - n0, w->prune_area - a0,
                                                       w->prune_run - r0, w->prune_dir - d0,
                                                       w->prune_walk - k0, w->maxdepth};
                            g_leafnodes.fetch_add(w->nodes - n0, std::memory_order_relaxed);
                        }
                        w->nodes = n0; w->prune_area = a0; w->prune_run = r0;
                        w->prune_dir = d0; w->prune_walk = k0; w->maxdepth = md0;
                        w->last_reported = n0;
                        continue;
                    }
                    // discard the attempt and SPLIT the task instead
                    w->nodes = n0; w->prune_area = a0; w->prune_run = r0;
                    w->prune_dir = d0; w->prune_walk = k0; w->maxdepth = md0;
                    w->last_reported = n0;
                    w->has_found = false;
                    w->node_cap = (long long)4e18;
                    w->cut_depth = (long)(w->N - t.left) + g_split_k;   // absolute depth of the sub-cut
                    for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++)
                        w->walk[a][b] = t.walk_snap[a][b];
                    {
                        std::vector<Poly> pp = t.polys, pl = t.placed;
                        w->dfs(pp, t.left, pl);   // enqueues children; counts only above the sub-cut
                    }
                    w->cut_depth = -1;
                    // the above-sub-cut nodes stay in this worker's totals (counted once, this run)
                }
                g_nodes.fetch_add(w->nodes - w->last_reported, std::memory_order_relaxed);
                w->last_reported = w->nodes;
                g_done.fetch_add(1, std::memory_order_relaxed);
            });
        }
        // coordinator: report aggregate progress, and enforce the node cap
        {
            time_t t_last = time(nullptr);
            while (g_done.load(std::memory_order_relaxed) < threads) {
                struct timespec ts{0, 200000000};       // 200 ms
                nanosleep(&ts, nullptr);
                time_t now = time(nullptr);
                long long gn = g_nodes.load(std::memory_order_relaxed);
                if (cap_total > 0 && co_nodes + gn >= cap_total)
                    g_stop.store(true, std::memory_order_relaxed);
                if (now - t_last >= log_secs) {
                    t_last = now;
                    size_t nd, nq;
                    { std::lock_guard<std::mutex> lk(g_ckmutex); nd = g_leafdone.size(); }
                    { std::lock_guard<std::mutex> lk(g_qmutex); nq = g_queue.size(); }
                    printf("  [%s] par nodes~%lld  leaves %zu  queue %zu/%zu  threads %d  t=%lds\n",
                           name.c_str(), co_nodes + done_before + gn +
                               g_leafnodes.load(std::memory_order_relaxed), nd, g_dispatched, nq, threads,
                           (long)(now - t0));
                    fflush(stdout);
                    if (!ckpt_file.empty() && now - last_ckpt >= ckpt_secs) {
                        last_ckpt = now; par_save_ckpt(cd);
                    }
                }
            }
        }
        for (auto& th : pool) th.join();

        // Aggregate: coordinator (above the top cut) + this run's split overheads (in the worker
        // totals) + every LEAF task (from g_leafdone, which carries earlier runs' leaves too).
        // Leaves are restored out of the worker totals, so nothing is counted twice.
        nodes = co_nodes; prune_area = co_pa; prune_run = co_pr;
        prune_dir = co_pd; prune_walk = co_pw; maxdepth = co_md;
        for (const Search& w : workers) {
            nodes += w.nodes; prune_area += w.prune_area; prune_run += w.prune_run;
            prune_dir += w.prune_dir; prune_walk += w.prune_walk;
            if (w.maxdepth > maxdepth) maxdepth = w.maxdepth;
        }
        for (const auto& kv : g_leafdone) {
            const TaskDone& r = kv.second;
            nodes += r.nodes; prune_area += r.pa; prune_run += r.pr;
            prune_dir += r.pd; prune_walk += r.pw;
            if (r.md > maxdepth) maxdepth = r.md;
        }
        par_save_ckpt(cd);
        bool all_done;
        { std::lock_guard<std::mutex> lk(g_qmutex);
          all_done = g_lifo ? g_queue.empty() : (g_qhead >= g_queue.size()); }
        if (!g_found_any && !all_done) return "INCONCLUSIVE";   // cap hit / stopped early
        if (g_found_any) { found = g_found_tiling; has_found = true; return "FOUND_TILING"; }
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
    qd_sync_D();
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
        WALK_BASESIDE = (int)rd_long();
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
        fprintf(stderr, "P5 walk prune ON: baseside=%d, %ld base walks, %ld side walks\n", WALK_BASESIDE, nb, ns);
        // optional "CORNERS t0 t1 t2" section (P6): forced edge type at each side's two corners
        if (fscanf(fp, "%4095s", tok) == 1 && std::string(tok) == "CORNERS") {
            for (int i = 0; i < 3; i++) CORNER_TYPE[i] = (int)rd_long();
            CORNER_PRUNE = true;
            fprintf(stderr, "P6 corner-type prune ON: sides = {%d,%d,%d}  (0=a 1=b 2=c, -1=free)\n",
                    CORNER_TYPE[0], CORNER_TYPE[1], CORNER_TYPE[2]);
            // optional "BASEWORD <side> <n> <t1 ... tn>" section (P7): the full edge order on <side>
            if (fscanf(fp, "%4095s", tok) == 1 && std::string(tok) == "BASEWORD") {
                WORD_SIDE = (int)rd_long();
                long n = rd_long();
                long len[3] = {tile.a, tile.b, tile.c};
                long acc = 0;
                WORD_PREFIX.push_back(0);
                for (long i = 0; i < n; i++) {
                    int t = (int)rd_long();
                    if (t < 0 || t > 2) { fprintf(stderr, "FATAL: BASEWORD type out of range\n"); exit(6); }
                    WORD_SEQ.push_back(t);
                    acc += len[t];
                    WORD_PREFIX.push_back(acc);
                }
                WORD_PRUNE = true;
                fprintf(stderr, "P7 base-word prune ON: side=%d, %ld edges, total length %ld\n",
                        WORD_SIDE, n, acc);
            }
        }
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
    mpz_class p, q, d; qd_mpz(x, p, q, d);
    gmp_fprintf(f, "%Zd %Zd %Zd", p.get_mpz_t(), q.get_mpz_t(), d.get_mpz_t());
}

int main(int argc, char** argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: cengine <instance> [node_cap] [checkpoint_file]\n");
        fprintf(stderr, "       CENGINE_THREADS=K  run the parallel engine on K threads (K>1)\n");
        return 1;
    }
    std::string name = argv[1];
    long long cap = (argc > 2) ? atoll(argv[2]) : 2000000000LL;
    int threads = 1;
    if (const char* e = getenv("CENGINE_THREADS")) threads = atoi(e);
    if (const char* e = getenv("CENGINE_MRV")) g_mrv = (atoi(e) != 0);
    if (const char* e = getenv("CENGINE_P7")) g_p7 = (atoi(e) != 0);
    if (threads < 1) threads = 1;
    Search S;
    if (!make_instance(name, S.tile, S.target, S.N)) {
        fprintf(stderr, "unknown instance %s\n", name.c_str());
        return 1;
    }
    S.name = name;
    S.node_cap = cap;
    if (argc > 3) S.ckpt_file = argv[3];
    gmp_printf("instance %s: N=%ld D=%Zd cap=%lld threads=%d\n",
               name.c_str(), S.N, QD_D.get_mpz_t(), cap, threads);
    fflush(stdout);
    const char* r = (threads > 1) ? S.run_parallel(threads) : S.run();
    printf("RESULT %s nodes=%lld maxdepth=%ld pruneA=%lld pruneR=%lld pruneP4=%lld pruneP5=%lld\n", r, S.nodes,
           S.maxdepth, S.prune_area, S.prune_run, S.prune_dir, S.prune_walk);
    fflush(stdout);  // never lose a verdict to a buffered stream
#ifdef QD_CROSSCHECK
    fprintf(stderr, "CROSSCHECK fastpath_ops=%lld gmp_fallbacks=%lld (%.4f%%) -- all agreed\n",
            QD_CC_COUNT, QD_CC_SLOW,
            100.0 * (double)QD_CC_SLOW / (double)(QD_CC_COUNT + QD_CC_SLOW + 1));
#endif
    // a verdict makes the checkpoint meaningless; leaving it would make a rerun resume into a
    // finished search and report a partial count
    if (!S.ckpt_file.empty() && strcmp(r, "INCONCLUSIVE") != 0) remove(S.ckpt_file.c_str());
    if (S.has_found) {
        // sanitize: FILE:-instance names contain '/' and ':', which made fopen fail (NULL) and the
        // gmp_fprintf below segfault -- losing the buffered RESULT line with it
        std::string safe = name;
        for (size_t i = 0; i < safe.size(); i++)
            if (safe[i] == '/' || safe[i] == ':') safe[i] = '_';
        std::string fn = "tiling_" + safe + ".txt";
        FILE* f = fopen(fn.c_str(), "w");
        if (!f) {
            fprintf(stderr, "WARNING: cannot open %s -- dumping tiling to stdout\n", fn.c_str());
            f = stdout;
        }
        gmp_fprintf(f, "%s %ld %Zd\n", name.c_str(), S.N, QD_D.get_mpz_t());
        for (const Poly& t : S.found) {
            for (const Pt& p : t) {
                dump_qd(f, p.x); fprintf(f, "  ");
                dump_qd(f, p.y); fprintf(f, "  ");
            }
            fprintf(f, "\n");
        }
        if (f != stdout) fclose(f); else fflush(stdout);
        printf("tiling written to %s (verify with python3 reverify_c.py %s)\n", fn.c_str(), fn.c_str());
    }
    return 0;
}
