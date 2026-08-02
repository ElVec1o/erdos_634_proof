// Test the complete-corner-wall hypothesis against a REAL tiling.
// Reads an engine tiling dump (exact Q(sqrt D) vertices) and reports, for the base line y = 0:
//   - the base walk: the tile edges lying on the base, left to right, with their lengths;
//   - for every candidate cevian from the apex to a base point, whether it is a WALL
//     (i.e. fully partitioned into whole tile edges on both sides with no tile straddling it).
use std::fs;

#[derive(Clone, Copy, PartialEq, Debug)]
struct Q { p: i128, q: i128, r: i128 }          // (p + q*sqrt D)/r
fn q(p: i128, qq: i128, r: i128) -> Q {
    let g = gcd3(p.abs(), qq.abs(), r.abs()).max(1);
    let s = if r < 0 { -1 } else { 1 };
    Q { p: s * p / g, q: s * qq / g, r: s * r / g }
}
fn gcd(a: i128, b: i128) -> i128 { if b == 0 { a } else { gcd(b, a % b) } }
fn gcd3(a: i128, b: i128, c: i128) -> i128 { gcd(gcd(a, b), c) }
fn sub(x: Q, y: Q) -> Q { q(x.p * y.r - y.p * x.r, x.q * y.r - y.q * x.r, x.r * y.r) }
fn eqq(x: Q, y: Q) -> bool { x.p * y.r == y.p * x.r && x.q * y.r == y.q * x.r }
fn is_zero(x: Q) -> bool { x.p == 0 && x.q == 0 }
fn to_f(x: Q, d: f64) -> f64 { (x.p as f64 + x.q as f64 * d.sqrt()) / x.r as f64 }

fn main() {
    let path = std::env::args().nth(1).expect("usage: walls <tiling file> [D]");
    let txt = fs::read_to_string(&path).expect("read");
    let mut lines = txt.lines();
    let hdr: Vec<&str> = lines.next().unwrap().split_whitespace().collect();
    let n: usize = hdr[1].parse().unwrap();
    let d: i128 = hdr[2].parse().unwrap();
    let df = d as f64;
    println!("tiling {}  N={}  D={}", path, n, d);

    let mut tris: Vec<[(Q, Q); 3]> = Vec::new();
    for line in lines {
        let v: Vec<i128> = line.split_whitespace().filter_map(|s| s.parse().ok()).collect();
        if v.len() < 18 { continue; }
        let mut t = [(q(0,0,1), q(0,0,1)); 3];
        for i in 0..3 {
            t[i] = (q(v[i*6], v[i*6+1], v[i*6+2]), q(v[i*6+3], v[i*6+4], v[i*6+5]));
        }
        tris.push(t);
    }
    println!("parsed {} triangles", tris.len());

    // ---- base walk: every tile edge with both endpoints on y = 0 ----
    let mut segs: Vec<(f64, f64)> = Vec::new();
    for t in &tris {
        for i in 0..3 {
            let (p1, p2) = (t[i], t[(i + 1) % 3]);
            if is_zero(p1.1) && is_zero(p2.1) {
                let (x1, x2) = (to_f(p1.0, df), to_f(p2.0, df));
                segs.push((x1.min(x2), x1.max(x2)));
            }
        }
    }
    segs.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
    segs.dedup_by(|a, b| (a.0 - b.0).abs() < 1e-9 && (a.1 - b.1).abs() < 1e-9);
    println!("\nBASE WALK (left to right), lengths:");
    let mut walk = String::new();
    for s in &segs {
        let len = s.1 - s.0;
        let lab = if (len - 2.0).abs() < 1e-9 { "a" } else if (len - 3.0).abs() < 1e-9 { "b" }
                  else if (len - 4.0).abs() < 1e-9 { "c" } else { "?" };
        walk.push_str(lab);
        print!("  [{:.3},{:.3}]={:.3}{}", s.0, s.1, len, lab);
    }
    println!("\n  walk = {}", walk);

    // ---- auto-detect the target: extreme points of the whole vertex set ----
    let mut pts: Vec<(f64, f64)> = Vec::new();
    for t in &tris { for i in 0..3 { pts.push((to_f(t[i].0, df), to_f(t[i].1, df))); } }
    let ymax = pts.iter().cloned().fold(f64::MIN, |m, p| m.max(p.1));
    let xmin = segs.first().map(|s| s.0).unwrap_or(0.0);
    let xmax = segs.last().map(|s| s.1).unwrap_or(0.0);
    let apex = pts.iter().cloned().find(|p| (p.1 - ymax).abs() < 1e-9).unwrap();
    println!("\ntarget: base [{:.3},{:.3}] on y=0, apex ({:.3},{:.3}); base length {:.3}",
             xmin, xmax, apex.0, apex.1, xmax - xmin);

    // ---- wall test at EVERY base vertex that occurs ----
    println!("\nWALL TEST: cevian from apex to each base junction (no tile may straddle):");
    let mut xs: Vec<f64> = segs.iter().map(|s| s.0).collect();
    xs.push(xmax);
    xs.dedup_by(|a, b| (*a - *b).abs() < 1e-9);
    let mut walls: Vec<f64> = Vec::new();
    for &x0 in &xs {
        if (x0 - xmin).abs() < 1e-9 || (x0 - xmax).abs() < 1e-9 { continue; }
        let (ax, ay) = apex;
        let (dx, dy) = (x0 - ax, 0.0 - ay);
        let mut straddlers = 0;
        for t in &tris {
            let (mut pos, mut neg) = (false, false);
            for i in 0..3 {
                let (px, py) = (to_f(t[i].0, df), to_f(t[i].1, df));
                let cross = dx * (py - ay) - dy * (px - ax);
                if cross > 1e-9 { pos = true; }
                if cross < -1e-9 { neg = true; }
            }
            if pos && neg { straddlers += 1; }
        }
        if straddlers == 0 { walls.push(x0); }
        println!("   x0={:<8.3} (dist from left {:>7.3}, from right {:>7.3})  straddlers {:<3} {}",
                 x0, x0 - xmin, xmax - x0, straddlers,
                 if straddlers == 0 { "<== WALL" } else { "" });
    }
    println!("\n  walls found at: {:?}", walls);
    println!("  left corner  has a wall: {}", walls.iter().any(|&w| w - xmin < (xmax - xmin) / 2.0));
    println!("  right corner has a wall: {}", walls.iter().any(|&w| xmax - w < (xmax - xmin) / 2.0));
}
