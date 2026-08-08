//! Exact arithmetic in Q(sqrt D), matching the C++ engine's `QD` so that instance files are shared.
//!
//! A value is `(p + q*sqrt(D)) / d` with `d > 0` and `gcd(p,q,d) = 1`. All fields are `i128`;
//! the coordinates arising in these targets stay far inside that range, and every operation
//! normalises, so representations are canonical and equality is structural.

pub static mut D: i128 = 0;

#[inline]
pub fn d_val() -> i128 {
    unsafe { D }
}

/// Binary GCD (Stein). The Euclidean version's `%` on `i128` dominated the finder's runtime:
/// normalisation runs on every single arithmetic operation.
fn g2(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    if a == 0 { return b }
    if b == 0 { return a }
    let sh = (a | b).trailing_zeros();
    a >>= a.trailing_zeros();
    loop {
        b >>= b.trailing_zeros();
        if a > b { std::mem::swap(&mut a, &mut b) }
        b -= a;
        if b == 0 { break }
    }
    a << sh
}

fn gcd3(a: i128, b: i128, c: i128) -> i128 {
    g2(g2(a, b), c)
}

#[inline]
fn ovf(v: Option<i128>) -> i128 {
    match v {
        Some(x) => x,
        None => {
            eprintln!("FATAL: i128 overflow in Q(sqrt D) arithmetic -- instance too large for this \
                       representation. Results would be unsound; aborting rather than continuing.");
            std::process::abort()
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Qd {
    pub p: i128,
    pub q: i128,
    pub d: i128,
}

impl Qd {
    pub fn new(p: i128, q: i128, d: i128) -> Qd {
        let mut v = Qd { p, q, d };
        v.norm();
        v
    }
    pub fn int(n: i128) -> Qd {
        Qd { p: n, q: 0, d: 1 }
    }
    pub fn zero() -> Qd {
        Qd { p: 0, q: 0, d: 1 }
    }
    fn norm(&mut self) {
        if self.d < 0 {
            self.p = -self.p;
            self.q = -self.q;
            self.d = -self.d;
        }
        if self.p == 0 && self.q == 0 {
            self.d = 1;
            return;
        }
        let g = gcd3(self.p, self.q, self.d);
        if g > 1 {
            self.p /= g;
            self.q /= g;
            self.d /= g;
        }
    }
    pub fn add(self, o: Qd) -> Qd {
        if self.d == 1 && o.d == 1 {
            return Qd { p: self.p + o.p, q: self.q + o.q, d: 1 }; // already canonical
        }
        if self.d == o.d {
            return Qd::new(self.p + o.p, self.q + o.q, self.d);
        }
        Qd::new(self.p * o.d + o.p * self.d, self.q * o.d + o.q * self.d, self.d * o.d)
    }
    pub fn sub(self, o: Qd) -> Qd {
        if self.d == 1 && o.d == 1 {
            return Qd { p: self.p - o.p, q: self.q - o.q, d: 1 };
        }
        if self.d == o.d {
            return Qd::new(self.p - o.p, self.q - o.q, self.d);
        }
        Qd::new(self.p * o.d - o.p * self.d, self.q * o.d - o.q * self.d, self.d * o.d)
    }
    pub fn mul(self, o: Qd) -> Qd {
        // (a + b w)(c + e w) = (ac + be D) + (ae + bc) w
        //
        // Checked throughout. Denominators reach ~1e14 on the larger instances, so an unchecked
        // i128 product can wrap silently -- and `verify()` runs on this same arithmetic, so a wrap
        // could make a bad tiling pass. Aborting is the only safe failure here.
        let p = ovf(ovf(self.p.checked_mul(o.p)).checked_add(ovf(ovf(self.q.checked_mul(o.q)).checked_mul(d_val()))));
        let q = ovf(ovf(self.p.checked_mul(o.q)).checked_add(ovf(self.q.checked_mul(o.p))));
        if self.d == 1 && o.d == 1 {
            return Qd { p, q, d: 1 };
        }
        Qd::new(p, q, ovf(self.d.checked_mul(o.d)))
    }
    pub fn neg(self) -> Qd {
        Qd { p: -self.p, q: -self.q, d: self.d }
    }
    pub fn is_zero(self) -> bool {
        self.p == 0 && self.q == 0
    }
    /// Sign of `p + q*sqrt(D)` (the denominator is positive), by comparing squares.
    pub fn sign(self) -> i32 {
        let (p, q) = (self.p, self.q);
        if q == 0 {
            return if p > 0 { 1 } else if p < 0 { -1 } else { 0 };
        }
        if p == 0 {
            return if q > 0 { 1 } else { -1 };
        }
        if p > 0 && q > 0 {
            return 1;
        }
        if p < 0 && q < 0 {
            return -1;
        }
        // opposite signs: compare p^2 with q^2 * D
        let lhs = p.saturating_mul(p);
        let rhs = q.saturating_mul(q).saturating_mul(d_val());
        let bigger_p = lhs > rhs;
        if p > 0 {
            // p > 0, q < 0 : positive iff p^2 > q^2 D
            if bigger_p { 1 } else if lhs == rhs { 0 } else { -1 }
        } else {
            if bigger_p { -1 } else if lhs == rhs { 0 } else { 1 }
        }
    }
    pub fn cmp_to(self, o: Qd) -> std::cmp::Ordering {
        use std::cmp::Ordering::*;
        match self.sub(o).sign() {
            1 => Greater,
            -1 => Less,
            _ => Equal,
        }
    }
}

impl PartialEq for Qd {
    fn eq(&self, o: &Qd) -> bool {
        self.p == o.p && self.q == o.q && self.d == o.d
    }
}
impl Eq for Qd {}
impl PartialOrd for Qd {
    fn partial_cmp(&self, o: &Qd) -> Option<std::cmp::Ordering> {
        Some(self.cmp_to(*o))
    }
}
impl Ord for Qd {
    fn cmp(&self, o: &Qd) -> std::cmp::Ordering {
        self.cmp_to(*o)
    }
}

/// A point of the plane over `Q(sqrt D)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Pt {
    pub x: Qd,
    pub y: Qd,
}

impl Pt {
    pub fn new(x: Qd, y: Qd) -> Pt {
        Pt { x, y }
    }
    pub fn sub(self, o: Pt) -> Pt {
        Pt::new(self.x.sub(o.x), self.y.sub(o.y))
    }
    pub fn add(self, o: Pt) -> Pt {
        Pt::new(self.x.add(o.x), self.y.add(o.y))
    }
}

/// Key for ordering points: lexicographic by (x, y). Used for canonical vertex choice and maps.
impl PartialOrd for Pt {
    fn partial_cmp(&self, o: &Pt) -> Option<std::cmp::Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for Pt {
    fn cmp(&self, o: &Pt) -> std::cmp::Ordering {
        match self.x.cmp_to(o.x) {
            std::cmp::Ordering::Equal => self.y.cmp_to(o.y),
            v => v,
        }
    }
}

/// `cross(o->a, o->b)`, positive when `o,a,b` turn left.
pub fn cross(o: Pt, a: Pt, b: Pt) -> Qd {
    let ax = a.x.sub(o.x);
    let ay = a.y.sub(o.y);
    let bx = b.x.sub(o.x);
    let by = b.y.sub(o.y);
    ax.mul(by).sub(ay.mul(bx))
}

/// Squared length of `p->q`.
pub fn dist2(p: Pt, q: Pt) -> Qd {
    let dx = q.x.sub(p.x);
    let dy = q.y.sub(p.y);
    dx.mul(dx).add(dy.mul(dy))
}

/// Twice the signed area of a simple polygon.
pub fn area2(poly: &[Pt]) -> Qd {
    let n = poly.len();
    let mut s = Qd::zero();
    for i in 0..n {
        let a = poly[i];
        let b = poly[(i + 1) % n];
        s = s.add(a.x.mul(b.y).sub(a.y.mul(b.x)));
    }
    s
}

/// Is `p` strictly between `a` and `b` on the segment `ab` (collinearity assumed checked)?
pub fn strictly_between(p: Pt, a: Pt, b: Pt) -> bool {
    if !cross(a, b, p).is_zero() {
        return false;
    }
    if p == a || p == b {
        return false;
    }
    // dot(p-a, b-a) > 0 and dot(p-b, a-b) > 0
    let d1 = p.x.sub(a.x).mul(b.x.sub(a.x)).add(p.y.sub(a.y).mul(b.y.sub(a.y)));
    let d2 = p.x.sub(b.x).mul(a.x.sub(b.x)).add(p.y.sub(b.y).mul(a.y.sub(b.y)));
    d1.sign() > 0 && d2.sign() > 0
}
