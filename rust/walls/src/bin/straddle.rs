// Rule 3 falsification of the DREAM LEMMA for hyp:walls:
//
//   (DL)  If a segment L in the tiling carries a whole b-edge at each end, then no tile
//         straddles L (so L partitions into whole tile edges on both sides).
//
// (DL) is what would make the walk arithmetic applicable to L, which is what rem:live says is
// missing. We test it against the genuine tilings: find every maximal collinear run of b-edges,
// and check whether any tile has interior on both sides of the line through it.
use std::fs;

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let path = &a[0];
    let bl: f64 = a[1].parse().unwrap();            // the tile's b-edge length
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

    // every b-edge in the tiling
    let mut bedges: Vec<((f64, f64), (f64, f64))> = Vec::new();
    for t in &tris {
        for i in 0..3 {
            let (p, q) = (t[i], t[(i + 1) % 3]);
            let len = (p.0 - q.0).hypot(p.1 - q.1);
            if (len - bl).abs() < 1e-7 { bedges.push((p, q)); }
        }
    }
    println!("{}  tiles {}  b-edges {}", path.rsplit('/').next().unwrap(), tris.len(), bedges.len());

    // for each b-edge, take the line through it and count straddling tiles
    let mut tested = 0; let mut with_straddle = 0; let mut worst = 0;
    for (p, q) in &bedges {
        let (dx, dy) = (q.0 - p.0, q.1 - p.1);
        let mut straddle = 0;
        for t in &tris {
            let (mut pos, mut neg) = (false, false);
            for i in 0..3 {
                let cr = dx * (t[i].1 - p.1) - dy * (t[i].0 - p.0);
                if cr > 1e-7 { pos = true; }
                if cr < -1e-7 { neg = true; }
            }
            // a tile straddles the LINE; restrict to those actually overlapping the segment's span
            if pos && neg {
                let cen = ((t[0].0 + t[1].0 + t[2].0) / 3.0, (t[0].1 + t[1].1 + t[2].1) / 3.0);
                let proj = ((cen.0 - p.0) * dx + (cen.1 - p.1) * dy) / (dx * dx + dy * dy);
                if proj > -0.5 && proj < 1.5 { straddle += 1; }
            }
        }
        tested += 1;
        if straddle > 0 { with_straddle += 1; if straddle > worst { worst = straddle; } }
    }
    println!("   b-edge lines tested {}   with a straddling tile near the segment: {}   worst {}",
             tested, with_straddle, worst);
    println!("   => dream lemma (DL) {}", if with_straddle == 0 { "SURVIVES on this tiling" } else { "*** FALSIFIED on this tiling ***" });
}
