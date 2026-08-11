//! Exact arithmetic in Q(sqrt D): every quantity is p + q*sqrt(D) with p,q rational.
//! Rationals are i128 fractions kept in lowest terms; all comparisons are exact.

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Rat {
    pub n: i128,
    pub d: i128, // always > 0, gcd(|n|,d) = 1
}

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    if a == 0 {
        1
    } else {
        a
    }
}

impl Rat {
    pub fn new(n: i128, d: i128) -> Self {
        assert!(d != 0, "zero denominator");
        let s = if d < 0 { -1 } else { 1 };
        let (n, d) = (n * s, d * s);
        let g = gcd(n, d);
        Rat { n: n / g, d: d / g }
    }
    pub fn int(n: i128) -> Self {
        Rat { n, d: 1 }
    }
    pub const ZERO: Rat = Rat { n: 0, d: 1 };
    pub fn is_zero(self) -> bool {
        self.n == 0
    }
    pub fn add(self, o: Rat) -> Rat {
        Rat::new(self.n * o.d + o.n * self.d, self.d * o.d)
    }
    pub fn sub(self, o: Rat) -> Rat {
        Rat::new(self.n * o.d - o.n * self.d, self.d * o.d)
    }
    pub fn mul(self, o: Rat) -> Rat {
        // cross-reduce first to keep i128 from overflowing on big constructions
        let g1 = gcd(self.n, o.d);
        let g2 = gcd(o.n, self.d);
        Rat::new((self.n / g1) * (o.n / g2), (self.d / g2) * (o.d / g1))
    }
    pub fn neg(self) -> Rat {
        Rat { n: -self.n, d: self.d }
    }
    pub fn sgn(self) -> i32 {
        if self.n > 0 {
            1
        } else if self.n < 0 {
            -1
        } else {
            0
        }
    }
}

/// value = a + b*sqrt(D), with D fixed per run (squarefree, > 1)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Alg {
    pub a: Rat,
    pub b: Rat,
}

impl Alg {
    pub fn rat(a: Rat) -> Self {
        Alg { a, b: Rat::ZERO }
    }
    pub fn int(n: i128) -> Self {
        Alg::rat(Rat::int(n))
    }
    pub const ZERO: Alg = Alg { a: Rat::ZERO, b: Rat::ZERO };
    pub fn add(self, o: Alg) -> Alg {
        Alg { a: self.a.add(o.a), b: self.b.add(o.b) }
    }
    pub fn sub(self, o: Alg) -> Alg {
        Alg { a: self.a.sub(o.a), b: self.b.sub(o.b) }
    }
    pub fn neg(self) -> Alg {
        Alg { a: self.a.neg(), b: self.b.neg() }
    }
    pub fn mul(self, o: Alg, d: i128) -> Alg {
        Alg {
            a: self.a.mul(o.a).add(self.b.mul(o.b).mul(Rat::int(d))),
            b: self.a.mul(o.b).add(self.b.mul(o.a)),
        }
    }
    pub fn is_zero(self) -> bool {
        self.a.is_zero() && self.b.is_zero()
    }
    /// exact sign of a + b*sqrt(D)
    pub fn sgn(self, d: i128) -> i32 {
        let (sa, sb) = (self.a.sgn(), self.b.sgn());
        if sb == 0 {
            return sa;
        }
        if sa == 0 {
            return sb;
        }
        if sa == sb {
            return sa;
        }
        // opposite signs: compare a^2 with D*b^2
        let a2 = self.a.mul(self.a);
        let db2 = self.b.mul(self.b).mul(Rat::int(d));
        let diff = a2.sub(db2); // > 0  <=>  |a| > sqrt(D)|b|
        let c = diff.sgn();
        if c == 0 {
            0
        } else if c > 0 {
            sa
        } else {
            sb
        }
    }
    pub fn nonneg(self, d: i128) -> bool {
        self.sgn(d) >= 0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Pt {
    pub x: Alg,
    pub y: Alg,
}

pub type Tri = [Pt; 3];

pub fn cross(o: Pt, p: Pt, q: Pt, d: i128) -> Alg {
    let ax = p.x.sub(o.x);
    let ay = p.y.sub(o.y);
    let bx = q.x.sub(o.x);
    let by = q.y.sub(o.y);
    ax.mul(by, d).sub(ay.mul(bx, d))
}

pub fn dist2(p: Pt, q: Pt, d: i128) -> Alg {
    let dx = q.x.sub(p.x);
    let dy = q.y.sub(p.y);
    dx.mul(dx, d).add(dy.mul(dy, d))
}
