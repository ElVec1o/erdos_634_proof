// Is the base-corner block COMPLETE in a real tiling?
// A corner block is the tile scaled by f (f a-feet, f^2 tiles) or by e (e c-feet, e^2 tiles);
// the two have equal footprint ef^2, and either may occur at either corner (a/c-feet duality).
// Complete <=> no tile straddles the block's boundary.
use std::fs;

fn main() {
    let arg: Vec<String> = std::env::args().skip(1).collect();
    let path = &arg[0];
    let e: f64 = arg[1].parse().unwrap();
    let f: f64 = arg[2].parse().unwrap();
    let txt = fs::read_to_string(path).expect("read");
    let mut lines = txt.lines();
    let hdr: Vec<&str> = lines.next().unwrap().split_whitespace().collect();
    let d: f64 = hdr[2].parse::<f64>().unwrap();
    let sq = d.sqrt();
    let qv = |p: f64, q: f64, r: f64| (p + q * sq) / r;

    let mut tris: Vec<[(f64, f64); 3]> = Vec::new();
    for line in lines {
        let v: Vec<f64> = line.split_whitespace().filter_map(|s| s.parse().ok()).collect();
        if v.len() < 18 { continue; }
        let mut t = [(0.0, 0.0); 3];
        for i in 0..3 { t[i] = (qv(v[i*6], v[i*6+1], v[i*6+2]), qv(v[i*6+3], v[i*6+4], v[i*6+5])); }
        tris.push(t);
    }
    let mut xs: Vec<f64> = Vec::new();
    for t in &tris { for i in 0..3 { if t[i].1.abs() < 1e-9 { xs.push(t[i].0); } } }
    let xmin = xs.iter().cloned().fold(f64::MAX, f64::min);
    let xmax = xs.iter().cloned().fold(f64::MIN, f64::max);

    let (ta, _tb, tc) = (e * f, f * f - e * e, f * f);
    let cosb = (e * (3.0 * f * f - e * e)) / (2.0 * f * f * f);
    let sinb = (1.0 - cosb * cosb).sqrt();
    let m = (xmax - xmin) / (e * (3.0 * f * f - e * e));
    println!("{}  N={}  tile=({},{},{})  m={:.0}",
             path.rsplit('/').next().unwrap(), tris.len(), ta, f*f - e*e, tc, m);

    let inside = |p: (f64, f64), tri: &[(f64, f64); 3]| -> f64 {
        let mut worst = f64::MAX;
        for i in 0..3 {
            let (x1, y1) = tri[i];
            let (x2, y2) = tri[(i + 1) % 3];
            let (x3, y3) = tri[(i + 2) % 3];
            let s = (x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1);
            let v = ((x2 - x1) * (p.1 - y1) - (y2 - y1) * (p.0 - x1)) * s.signum();
            worst = worst.min(v / ((x2 - x1).hypot(y2 - y1)));
        }
        worst
    };
    let mk = |x0: f64, dir: f64, base_side: f64, far: f64| {
        [(x0, 0.0), (x0 + dir * base_side, 0.0), (x0 + dir * far * cosb, far * sinb)]
    };
    let blocks = [
        ("LEFT  a-feet (x f)", mk(xmin, 1.0, f * ta, f * tc), f * f),
        ("LEFT  c-feet (x e)", mk(xmin, 1.0, e * tc, e * ta), e * e),
        ("RIGHT a-feet (x f)", mk(xmax, -1.0, f * ta, f * tc), f * f),
        ("RIGHT c-feet (x e)", mk(xmax, -1.0, e * tc, e * ta), e * e),
    ];
    let mut left_ok = false; let mut right_ok = false;
    for (name, blk, expect) in blocks {
        let (mut inn, mut straddle) = (0, 0);
        for t in &tris {
            let cen = ((t[0].0 + t[1].0 + t[2].0) / 3.0, (t[0].1 + t[1].1 + t[2].1) / 3.0);
            let cin = inside(cen, &blk) > 0.0;
            let ds: Vec<f64> = t.iter().map(|&p| inside(p, &blk)).collect();
            let allin = ds.iter().all(|&v| v > -1e-7);
            let allout = ds.iter().all(|&v| v < 1e-7);
            if cin { inn += 1; if !allin { straddle += 1; } } else if !allout { straddle += 1; }
        }
        let ok = straddle == 0 && (inn as f64 - expect).abs() < 0.5;
        if ok { if name.starts_with("LEFT") { left_ok = true; } else { right_ok = true; } }
        println!("   {:<20} tiles {:>3}/{:<3} straddling {:>3}  {}",
                 name, inn, expect, straddle, if ok { "COMPLETE" } else { "" });
    }
    println!("   => left corner complete: {:<5}   right corner complete: {}", left_ok, right_ok);
    if !left_ok || !right_ok { println!("   *** A CORNER BLOCK IS BROKEN IN A GENUINE TILING ***"); }
}
