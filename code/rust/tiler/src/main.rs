//! tiler — construct and exactly verify tilings of base-β regions (Erdős #634).
//!
//! Base-β member (e,f): tile (a,b,c) = (ef, f²−e², f²), angles (α,β,γ), γ = 2α+β, 3α+2β = π.
//! Unit target Δ₁: isosceles, base Y₁ = e(3f²−e²), legs X₁ = f³, N₁ = 3f²−e² tiles.
//!
//! Lattice basis  u = (1,0),  w = (cos β, sin β);  cos β = eN₁/(2f³), so X₁cos β = Y₁/2.
//! In these coordinates the a×c cell is the b-glued 2-tile parallelogram Q_b, and
//! Δ_M is exactly the triangle (0,0), (M·Y₁,0), (0,M·X₁).
//!
//! Subcommands
//!   pgram   <f>            e = 1 unit parallelogram (Λ + strip + shifted Λ)   — known theorem
//!   delta   <e> <f> <M>    candidate construction of Δ_M                      — under study
//!   probe   <file> <e> <f> read an engine witness, report it in lattice coords
//!
//! Verification is exact in Q(√D): C1 congruence, C2 containment, C3 pairwise separation,
//! C4 area. C3 is the heavy part (O(N²) exact predicates) — it reports progress and an ETA.

mod alg;
mod cert;
use alg::*;
use std::env;
use std::fs;
use std::time::Instant;

/// member data
#[derive(Clone, Copy)]
struct Member {
    e: i128,
    f: i128,
    a: i128,
    b: i128,
    c: i128,
    n1: i128,
    y1: i128,
    x1: i128,
    d: i128,
    cosb: Rat,
    sinb: Rat, // sin β = sinb * sqrt(D)
}

fn squarefree_split(mut n: i128) -> (i128, i128) {
    // n = sq^2 * rest, rest squarefree
    let mut sq = 1i128;
    let mut k = 2i128;
    while k * k <= n {
        while n % (k * k) == 0 {
            n /= k * k;
            sq *= k;
        }
        k += 1;
    }
    (sq, n)
}

impl Member {
    fn new(e: i128, f: i128) -> Self {
        let (a, b, c) = (e * f, f * f - e * e, f * f);
        let n1 = 3 * f * f - e * e;
        let (y1, x1) = (e * n1, f * f * f);
        // cos β = e·N₁/(2f³);  sin²β = 1 − cos²β
        let cosb = Rat::new(e * n1, 2 * f * f * f);
        let s2 = Rat::int(1).sub(cosb.mul(cosb)); // = num/den
        // sin β = sqrt(num/den) = sqrt(num*den)/den ; split num*den = sq² · D
        let (sq, dd) = squarefree_split(s2.n * s2.d);
        let sinb = Rat::new(sq, s2.d);
        assert_eq!(sinb.mul(sinb).mul(Rat::int(dd)), s2, "sin β decomposition");
        Member { e, f, a, b, c, n1, y1, x1, d: dd, cosb, sinb }
    }
    /// lattice coords (uu, ww) -> plane point  uu·u + ww·w
    fn pt(&self, uu: Rat, ww: Rat) -> Pt {
        Pt {
            x: Alg::rat(uu.add(ww.mul(self.cosb))),
            y: Alg { a: Rat::ZERO, b: ww.mul(self.sinb) },
        }
    }
    fn pti(&self, uu: i128, ww: i128) -> Pt {
        self.pt(Rat::int(uu), Rat::int(ww))
    }
}

/// the two tiles of the a×c cell with lower-left corner at (u0, w0); split on the b-diagonal
fn cell(m: &Member, u0: i128, w0: i128) -> (Tri, Tri) {
    let a = m.pti(u0, w0);
    let b = m.pti(u0 + m.a, w0);
    let c = m.pti(u0 + m.a, w0 + m.c);
    let d = m.pti(u0, w0 + m.c);
    ([a, b, d], [b, c, d])
}

/// Λ: staircase right triangle with legs p·a (u) and p·c (w), apex at (0,0)-corner style:
/// vertices (u0,w0), (u0+p·a, w0), (u0, w0+p·c). Cells with i+j ≤ p−2 whole, i+j = p−1 halved.
fn staircase(m: &Member, u0: i128, w0: i128, p: i128, out: &mut Vec<Tri>) {
    for i in 0..p {
        for j in 0..p {
            if i + j <= p - 2 {
                let (t1, t2) = cell(m, u0 + i * m.a, w0 + j * m.c);
                out.push(t1);
                out.push(t2);
            } else if i + j == p - 1 {
                let (t1, _) = cell(m, u0 + i * m.a, w0 + j * m.c);
                out.push(t1);
            }
        }
    }
}

/// the e = 1 unit parallelogram: Λ + strip(b copies of Q_c) + Λ-staircase shifted by b
fn build_pgram(m: &Member) -> Vec<Tri> {
    assert_eq!(m.e, 1, "pgram construction is the e = 1 family");
    let mut out = Vec::new();
    let (f, a, b) = (m.f, m.a, m.b);
    // Λ
    staircase(m, 0, 0, f, &mut out);
    // strip: step σ = (X₁w − f·a·u)/b, lattice coords (−f²/b, f³/b)
    let du = Rat::new(-f * f, b);
    let dw = Rat::new(f * f * f, b);
    for k in 0..b {
        let u0 = Rat::int(f * a).add(du.mul(Rat::int(k)));
        let w0 = dw.mul(Rat::int(k));
        let v0 = m.pt(u0, w0);
        let v1 = m.pt(u0.add(Rat::int(b)), w0);
        let v2 = m.pt(u0.add(Rat::int(b)).add(du), w0.add(dw));
        let v3 = m.pt(u0.add(du), w0.add(dw));
        out.push([v0, v1, v2]);
        out.push([v0, v2, v3]);
    }
    // Ρ: the complementary staircase in the lattice shifted by b, out to u = Y₁
    let ncols = (m.y1 - b) / a;
    for j in 0..f {
        for i in 0..ncols {
            let u_lo = b + i * a;
            if u_lo >= f * a + b - j * a {
                let (t1, t2) = cell(m, u_lo, j * m.c);
                out.push(t1);
                out.push(t2);
            } else if u_lo == f * a + b - (j + 1) * a {
                let (_, t2) = cell(m, u_lo, j * m.c);
                out.push(t2);
            }
        }
    }
    out
}

/// region a tiling is checked against
enum Region {
    /// parallelogram 0, (Y,0), (Y,X), (0,X) in lattice coords
    Pgram(i128, i128),
    /// triangle (0,0), (Y,0), (0,X) in lattice coords  (= Δ_M for Y = M·Y₁, X = M·X₁)
    Tri(i128, i128),
}

fn region_pts(m: &Member, r: &Region) -> Vec<Pt> {
    match *r {
        Region::Pgram(y, x) => vec![m.pti(0, 0), m.pti(y, 0), m.pti(y, x), m.pti(0, x)],
        Region::Tri(y, x) => vec![m.pti(0, 0), m.pti(y, 0), m.pti(0, x)],
    }
}

fn verify(m: &Member, tiles: &mut Vec<Tri>, r: &Region, verbose: bool) -> Result<(), String> {
    let d = m.d;
    let sq: Vec<i128> = {
        let mut v = vec![m.a * m.a, m.b * m.b, m.c * m.c];
        v.sort();
        v
    };
    // C1
    for (idx, t) in tiles.iter().enumerate() {
        let mut ds: Vec<Alg> = (0..3).map(|i| dist2(t[i], t[(i + 1) % 3], d)).collect();
        for x in &ds {
            if !x.b.is_zero() {
                return Err(format!("C1 tile {idx}: irrational side²"));
            }
        }
        ds.sort_by(|p, q| (p.a.n * q.a.d).cmp(&(q.a.n * p.a.d)));
        let got: Vec<i128> = ds.iter().map(|x| if x.a.d == 1 { x.a.n } else { -1 }).collect();
        if got != sq {
            return Err(format!("C1 tile {idx}: sides² {got:?} != {sq:?}"));
        }
    }
    // orient CCW
    for t in tiles.iter_mut() {
        if cross(t[0], t[1], t[2], d).sgn(d) < 0 {
            t.swap(1, 2);
        }
    }
    // C2 containment
    let poly = region_pts(m, r);
    let k = poly.len();
    for (idx, t) in tiles.iter().enumerate() {
        for v in t.iter() {
            for i in 0..k {
                if !cross(poly[i], poly[(i + 1) % k], *v, d).nonneg(d) {
                    return Err(format!("C2 tile {idx}: vertex outside region"));
                }
            }
        }
    }
    // C4 area
    let mut tot = Alg::ZERO;
    for t in tiles.iter() {
        tot = tot.add(cross(t[0], t[1], t[2], d));
    }
    let mut ra = Alg::ZERO;
    for i in 1..k - 1 {
        ra = ra.add(cross(poly[0], poly[i], poly[i + 1], d));
    }
    if tot != ra {
        return Err(format!("C4 area mismatch: {:?} vs {:?}", tot, ra));
    }
    // C3 pairwise separation (heavy)
    let n = tiles.len();
    let total_pairs = (n as u64) * (n as u64 - 1) / 2;
    let t0 = Instant::now();
    let mut done: u64 = 0;
    let mut next_report = total_pairs / 10;
    for i in 0..n {
        for j in (i + 1)..n {
            let (aa, bb) = (&tiles[i], &tiles[j]);
            let mut ok = false;
            'outer: for src in [aa, bb] {
                for k2 in 0..3 {
                    let (p, q) = (src[k2], src[(k2 + 1) % 3]);
                    let sa: Vec<i32> = aa.iter().map(|v| cross(p, q, *v, d).sgn(d)).collect();
                    let sb: Vec<i32> = bb.iter().map(|v| cross(p, q, *v, d).sgn(d)).collect();
                    let a_nn = sa.iter().all(|&s| s >= 0);
                    let a_np = sa.iter().all(|&s| s <= 0);
                    let b_nn = sb.iter().all(|&s| s >= 0);
                    let b_np = sb.iter().all(|&s| s <= 0);
                    if (a_nn && b_np) || (a_np && b_nn) {
                        ok = true;
                        break 'outer;
                    }
                }
            }
            if !ok {
                return Err(format!("C3 overlap: tiles {i},{j}"));
            }
            done += 1;
            if verbose && done >= next_report && total_pairs > 200_000 {
                let el = t0.elapsed().as_secs_f64();
                let frac = done as f64 / total_pairs as f64;
                eprintln!(
                    "    C3 {:.0}%  {}/{} pairs  {:.1}s elapsed  ETA {:.1}s",
                    frac * 100.0,
                    done,
                    total_pairs,
                    el,
                    el / frac - el
                );
                next_report += total_pairs / 10;
            }
        }
    }
    Ok(())
}

fn parse_witness(path: &str, m: &Member) -> Vec<Tri> {
    let txt = fs::read_to_string(path).expect("read witness");
    let mut out = Vec::new();
    for line in txt.lines().skip(1) {
        let tk: Vec<i128> = line
            .split_whitespace()
            .filter_map(|s| s.parse::<i128>().ok())
            .collect();
        if tk.len() != 18 {
            continue;
        }
        let mut vs = [Pt { x: Alg::ZERO, y: Alg::ZERO }; 3];
        for k in 0..3 {
            let (p, q, r, s, t, u) = (tk[6 * k], tk[6 * k + 1], tk[6 * k + 2], tk[6 * k + 3], tk[6 * k + 4], tk[6 * k + 5]);
            vs[k] = Pt {
                x: Alg { a: Rat::new(p, r), b: Rat::new(q, r) },
                y: Alg { a: Rat::new(s, u), b: Rat::new(t, u) },
            };
        }
        out.push(vs);
    }
    let _ = m;
    out
}

/// report a witness in lattice coordinates: w = y/sin β, u = x − w·cos β
fn probe(path: &str, m: &Member) {
    let tiles = parse_witness(path, m);
    println!("probe {}: {} tiles, member (e,f)=({},{}), D={}", path, tiles.len(), m.e, m.f, m.d);
    let mut lat = 0usize;
    let mut dens: Vec<i128> = Vec::new();
    for t in &tiles {
        let mut is_lat = true;
        for v in t.iter() {
            // y = w·sinb·√D  => w = y.b / sinb   (y is a pure √D multiple)
            let w = v.y.b.mul(Rat::new(m.sinb.d, m.sinb.n));
            let u = v.x.a.sub(w.mul(m.cosb));
            if u.d != 1 || w.d != 1 {
                is_lat = false;
            }
            dens.push(u.d);
            dens.push(w.d);
        }
        if is_lat {
            lat += 1;
        }
    }
    dens.sort();
    dens.dedup();
    println!("  lattice-coordinate tiles: {} / {}   off-lattice: {}", lat, tiles.len(), tiles.len() - lat);
    println!("  denominators present: {:?}   (b = {}, f·b = {})", dens, m.b, m.f * m.b);
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: tiler pgram <f> | tiler probe <file> <e> <f> | tiler cert <instance> <witness> <out.lean> <Namespace>");
        return;
    }
    match args[1].as_str() {
        "pgram" => {
            let fs_: Vec<i128> = args[2..].iter().map(|s| s.parse().unwrap()).collect();
            for f in fs_ {
                let m = Member::new(1, f);
                let mut t = build_pgram(&m);
                let want = 2 * m.n1;
                print!("f={:<3} tiles {:>5} (want {:>5})  D={:<5} ", f, t.len(), want, m.d);
                if t.len() as i128 != want {
                    println!("COUNT MISMATCH");
                    continue;
                }
                let t0 = Instant::now();
                match verify(&m, &mut t, &Region::Pgram(m.y1, m.x1), true) {
                    Ok(()) => println!("VERIFIED  ({:.2}s)", t0.elapsed().as_secs_f64()),
                    Err(e) => println!("FAILED: {e}"),
                }
            }
        }
        "probe" => {
            let (e, f): (i128, i128) = (args[3].parse().unwrap(), args[4].parse().unwrap());
            probe(&args[2], &Member::new(e, f));
        }
        "cert" => {
            // tiler cert <instance> <witness> <out.lean> <Namespace>
            if args.len() < 6 {
                eprintln!("usage: tiler cert <instance> <witness> <out.lean> <Namespace>");
                return;
            }
            match cert::generate(&args[2], &args[3], &args[4], &args[5]) {
                Ok(()) => println!("certificate OK"),
                Err(e) => println!("FAILED: {e}"),
            }
        }
        "seed" => {
            // tiler seed <e> <f> <M> : emit the SEED section for Δ_M — every a×c lattice cell that
            // lies wholly inside the triangle (0,0),(M·Y₁,0),(0,M·X₁) in lattice coordinates,
            // each split on its b-diagonal into two tiles. Engine format: x,y as (p + q√D)/r.
            let (e, f, mm): (i128, i128, i128) =
                (args[2].parse().unwrap(), args[3].parse().unwrap(), args[4].parse().unwrap());
            let m = Member::new(e, f);
            let (bu, bw) = (mm * m.y1, mm * m.x1);          // legs in lattice units
            let den = 2 * f * f * f;                        // cos β = e·N₁/(2f³), sin β = sinb√D
            let (cn, cd) = (m.cosb.n, m.cosb.d);
            let (sn, sd) = (m.sinb.n, m.sinb.d);
            let mut out: Vec<String> = Vec::new();
            let mut cells = 0i128;
            let mut j = 0i128;
            while (j + 1) * m.c <= bw {
                let mut i = 0i128;
                while (i + 1) * m.a <= bu {
                    // far corner inside?  u/bu + w/bw <= 1
                    let (u, w) = ((i + 1) * m.a, (j + 1) * m.c);
                    let marg: i128 = if args.len() > 5 { args[5].parse().unwrap() } else { 0 };
                    if (u * bw + w * bu) * 100 <= bu * bw * (100 - marg) {
                        let corner = |uu: i128, ww: i128| -> String {
                            // x = uu + ww·cosb = (uu·cd + ww·cn)/cd ; y = ww·sinb·√D = (ww·sn)√D/sd
                            format!("{} 0 {}  0 {} {}", uu * cd + ww * cn, cd, ww * sn, sd)
                        };
                        let (a0, b0) = (i * m.a, j * m.c);
                        let (a1, b1) = ((i + 1) * m.a, (j + 1) * m.c);
                        // cell A=(a0,b0) B=(a1,b0) C=(a1,b1) D=(a0,b1); split on B–D (length b)
                        out.push(format!("{}  {}  {}", corner(a0, b0), corner(a1, b0), corner(a0, b1)));
                        out.push(format!("{}  {}  {}", corner(a1, b0), corner(a1, b1), corner(a0, b1)));
                        cells += 1;
                    }
                    i += 1;
                }
                j += 1;
            }
            let _ = den;
            eprintln!("seed: {} cells = {} tiles (of {} total)", cells, out.len(), mm * mm * m.n1);
            println!("SEED {}", out.len());
            for l in out { println!("{}", l); }
        }
        "seedqc" => {
            // tiler seedqc <e> <f> <M> : seed from the Q_c lattice (cells = two tiles glued along c,
            // sides a and b, angle α+β).  In these coordinates Δ_M is the triangle (0,0), (B,0),
            // (Mf,Mf) with B = M·N₁/f — integral exactly when f | M.  cos(α+β) = e/(2f) and
            // sin(α+β) = √(4f²−e²)/(2f), so a lattice point (i,j) is
            //     x = (2f·i·a + j·b·e)/(2f),   y = (j·b·k)·√D/(2f)   where 4f²−e² = k²·D.
            let (e, f, mm): (i128, i128, i128) =
                (args[2].parse().unwrap(), args[3].parse().unwrap(), args[4].parse().unwrap());
            let m = Member::new(e, f);
            assert_eq!(mm % f, 0, "Q_c seeding needs f | M");
            let b_cols = mm * m.n1 / f;
            let apex = mm * f;
            let (sq, dd) = squarefree_split(4 * f * f - e * e);
            assert_eq!(dd, m.d, "sqrt(4f^2-e^2) must live in the same field");
            let den = 2 * f;
            let pt = |i: i128, j: i128| -> String {
                format!("{} 0 {}  0 {} {}", den * i * m.a + j * m.b * e, den, j * m.b * sq, den)
            };
            let mut out: Vec<String> = Vec::new();
            let mut cells = 0i128;
            for j in 0..apex {
                for i in 0..b_cols {
                    // fully inside: (j+1) <= i  and  apex*(i+1) + (b_cols-apex)*(j+1) <= apex*b_cols
                    if j + 1 <= i && apex * (i + 1) + (b_cols - apex) * (j + 1) <= apex * b_cols {
                        // split on the long diagonal (i,j)-(i+1,j+1), which has length c
                        out.push(format!("{}  {}  {}", pt(i, j), pt(i + 1, j), pt(i + 1, j + 1)));
                        out.push(format!("{}  {}  {}", pt(i, j), pt(i + 1, j + 1), pt(i, j + 1)));
                        cells += 1;
                    }
                }
            }
            eprintln!("seedqc: {} cells = {} tiles (of {} total)", cells, out.len(), mm * mm * m.n1);
            println!("SEED {}", out.len());
            for l in out { println!("{}", l); }
        }
        "delta" => {
            eprintln!("delta: construction under study — no candidate wired yet");
        }
        other => eprintln!("unknown subcommand {other}"),
    }
}
