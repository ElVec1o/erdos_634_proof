// Exact validator for an engine instance file over Q(sqrt D).
// Checks, with integer arithmetic only:  cos^2+sin^2 = 1 for each tile angle;
// gamma = 2*alpha + beta;  the three sides obey the law of cosines against the
// stated angles;  the target's vertices give side lengths as stated;  and
// 2*Area(target) = N * area2(tile).
use std::env;
use std::fs;

/// element (p + q*sqrt(D)) / r  of Q(sqrt D), kept unnormalized
#[derive(Clone, Copy, Debug)]
struct Qd { p: i128, q: i128, r: i128 }

fn qd(p: i128, q: i128, r: i128) -> Qd { Qd { p, q, r } }

fn add(x: Qd, y: Qd) -> Qd { qd(x.p * y.r + y.p * x.r, x.q * y.r + y.q * x.r, x.r * y.r) }
fn sub(x: Qd, y: Qd) -> Qd { qd(x.p * y.r - y.p * x.r, x.q * y.r - y.q * x.r, x.r * y.r) }
fn mul(x: Qd, y: Qd, d: i128) -> Qd {
    qd(x.p * y.p + d * x.q * y.q, x.p * y.q + x.q * y.p, x.r * y.r)
}
fn from_int(n: i128) -> Qd { qd(n, 0, 1) }
fn scale(x: Qd, n: i128) -> Qd { qd(x.p * n, x.q * n, x.r) }
/// exact equality of two unnormalized representatives
fn eq(x: Qd, y: Qd) -> bool { x.p * y.r == y.p * x.r && x.q * y.r == y.q * x.r }

fn main() {
    let path = env::args().nth(1).expect("usage: instcheck <instance file>");
    let txt = fs::read_to_string(&path).expect("cannot read");
    let mut t = txt.split_whitespace().map(|s| s.parse::<i128>().expect("int"));
    let mut next = || t.next().expect("truncated");

    let d = next();
    let (a, b, c) = (next(), next(), next());
    let mut cs = [qd(0, 0, 1); 3];
    let mut sn = [qd(0, 0, 1); 3];
    for i in 0..3 {
        cs[i] = qd(next(), next(), next());
        sn[i] = qd(next(), next(), next());
    }
    let area2 = qd(next(), next(), next());
    let n = next();
    let mut vx = [qd(0, 0, 1); 3];
    let mut vy = [qd(0, 0, 1); 3];
    for i in 0..3 {
        vx[i] = qd(next(), next(), next());
        vy[i] = qd(next(), next(), next());
    }

    let mut ok = true;
    let mut chk = |name: &str, cond: bool, ok: &mut bool| {
        println!("  {:<34} {}", name, if cond { "PASS" } else { "*** FAIL ***" });
        if !cond { *ok = false; }
    };

    println!("instance {}  D={}  tile=({},{},{})  N={}", path, d, a, b, c, n);

    // 1. unit circle for each angle
    for (i, nm) in ["alpha", "beta", "gamma"].iter().enumerate() {
        let s = add(mul(cs[i], cs[i], d), mul(sn[i], sn[i], d));
        chk(&format!("cos^2+sin^2 = 1 ({})", nm), eq(s, from_int(1)), &mut ok);
    }

    // 2. angle sum: alpha + beta + gamma = pi, i.e. cos(a+b) = -cos g and sin(a+b) = sin g.
    //    This holds for ANY triangle and is the check that must pass on every branch.
    let cab = sub(mul(cs[0], cs[1], d), mul(sn[0], sn[1], d));
    let sab = add(mul(sn[0], cs[1], d), mul(cs[0], sn[1], d));
    chk("alpha+beta+gamma = pi (cos)", eq(cab, scale(cs[2], -1)), &mut ok);
    chk("alpha+beta+gamma = pi (sin)", eq(sab, sn[2]), &mut ok);

    // informational: which branch is this tile in?
    let c2 = sub(mul(cs[0], cs[0], d), mul(sn[0], sn[0], d));
    let s2 = scale(mul(cs[0], sn[0], d), 2);
    let csum = sub(mul(c2, cs[1], d), mul(s2, sn[1], d));
    let ssum = add(mul(s2, cs[1], d), mul(c2, sn[1], d));
    let is3a2b = eq(csum, cs[2]) && eq(ssum, sn[2]);
    let is120 = eq(cs[2], qd(-1, 0, 2));
    println!("  {:<34} {}", "branch", if is3a2b { "3a+2b=pi (gamma = 2alpha+beta)" }
             else if is120 { "2pi/3 tile (gamma = 2pi/3)" } else { "OTHER" });

    // 3. law of cosines: a^2 = b^2+c^2-2bc cos(alpha), etc.
    let sides = [(a, b, c), (b, a, c), (c, a, b)];
    for (i, nm) in ["alpha", "beta", "gamma"].iter().enumerate() {
        let (o, u, v) = sides[i];
        let lhs = from_int(o * o);
        let rhs = sub(from_int(u * u + v * v), scale(cs[i], 2 * u * v));
        chk(&format!("law of cosines ({})", nm), eq(lhs, rhs), &mut ok);
    }

    // 4. tile area2 = b*c*sin(alpha)
    chk("area2 = b*c*sin(alpha)", eq(area2, scale(sn[0], b * c)), &mut ok);

    // 5. target: 2*Area = |cross product of two edges|, and = N * area2
    let e1x = sub(vx[1], vx[0]); let e1y = sub(vy[1], vy[0]);
    let e2x = sub(vx[2], vx[0]); let e2y = sub(vy[2], vy[0]);
    let cross = sub(mul(e1x, e2y, d), mul(e1y, e2x, d));
    chk("2*Area(target) = N * area2(tile)", eq(cross, scale(area2, n)), &mut ok);

    // 6. report the three target side lengths squared (must be perfect squares of the sides)
    let mut sq = |ax: Qd, ay: Qd, bx: Qd, by: Qd| -> Qd {
        let dx = sub(bx, ax); let dy = sub(by, ay);
        add(mul(dx, dx, d), mul(dy, dy, d))
    };
    let l = [sq(vx[0], vy[0], vx[1], vy[1]), sq(vx[1], vy[1], vx[2], vy[2]), sq(vx[2], vy[2], vx[0], vy[0])];
    for (i, s) in l.iter().enumerate() {
        let rational = s.q == 0;
        let val = if rational { (s.p as f64) / (s.r as f64) } else { f64::NAN };
        println!("  side {} squared = ({} + {}*sqrt{})/{}   -> {}{}", i, s.p, s.q, d, s.r,
                 if rational { format!("{}", val.sqrt()) } else { "IRRATIONAL".into() },
                 if rational && (val.sqrt().round().powi(2) - val).abs() < 1e-6 { " (integer)" } else { "" });
    }

    println!("{}", if ok { "ALL EXACT CHECKS PASS" } else { "VALIDATION FAILED" });
    if !ok { std::process::exit(1); }
}
