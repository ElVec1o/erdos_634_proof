//! finder — a randomized tiling FINDER for the Erdos #634 instances.
//!
//! Purpose. The exhaustive engine (`engine/cengine`) is a deterministic depth-first search. That is
//! the right shape for proving EXHAUSTED, but a poor one for finding a tiling: it explores in a
//! fixed order and can sit in one barren subtree indefinitely (N=234 reached 4.0e7 nodes without a
//! verdict). Backtracking search on combinatorial problems has heavy-tailed runtime, and rapid
//! randomized restarts are the standard remedy (Gomes, Selman & Crato, *Heavy-tailed distributions
//! in combinatorial search*, CP 1997; Luby, Sinclair & Zuckerman, *Optimal speedup of Las Vegas
//! algorithms*, IPL 1993). This program is that: the same branching, randomized, restarted on a
//! Luby schedule, run as a parallel portfolio.
//!
//! Soundness. The finder is SOUND but deliberately INCOMPLETE: it may miss tilings, and finding
//! nothing proves nothing. Every tiling it reports is re-verified from scratch (congruence of all
//! N tiles, pairwise-disjoint interiors via the boundary algebra, exact area identity) before being
//! printed, so a bug yields a rejected candidate, never a false theorem. Exhaustion claims must
//! continue to come from `cengine`.
//!
//! Branching matches `cengine::placements`: at the lexicographically least vertex of a component
//! (always a convex corner, so any tiling puts a tile corner there), take unit vectors along the
//! two boundary rays, rotate by each of the three corner angles, and try both flank orders.

mod qd;
use qd::*;
use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::process;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;

// ------------------------------------------------------------------ instance ---

#[derive(Clone, Copy)]
struct Corner {
    cs: Qd,
    sn: Qd,
    l: [i128; 2], // the two flank lengths, in both orders
    m: [i128; 2],
}

#[derive(Clone)]
struct Instance {
    n: usize,
    corners: [Corner; 3],
    target: Vec<Pt>,
    area2_tile: Qd,
    /// cosine of the LARGEST tile angle's complement... in fact: cos of the smallest tile angle.
    /// A corner whose interior angle is below it admits no placement at all.
    cos_min: Qd,
}

fn parse_instance(path: &str) -> Instance {
    let text = fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("cannot read {path}: {e}");
        process::exit(1);
    });
    let mut it = text
        .split_whitespace()
        .take_while(|t| *t != "WALKS" && *t != "CORNERS")
        .map(|t| t.parse::<i128>().expect("non-integer token"));
    let mut next = || it.next().expect("instance file truncated");
    unsafe { D = next() };
    let (a, b, c) = (next(), next(), next());
    let adj: [[i128; 2]; 3] = [[b, c], [a, c], [a, b]];
    let mut rd_qd = |f: &mut dyn FnMut() -> i128| {
        let (p, q, d) = (f(), f(), f());
        Qd::new(p, q, d)
    };
    let mut corners = [Corner { cs: Qd::zero(), sn: Qd::zero(), l: [0; 2], m: [0; 2] }; 3];
    for i in 0..3 {
        let cs = rd_qd(&mut next);
        let sn = rd_qd(&mut next);
        corners[i] = Corner { cs, sn, l: [adj[i][0], adj[i][1]], m: [adj[i][1], adj[i][0]] };
    }
    let area2_tile = rd_qd(&mut next);
    let n = next() as usize;
    let mut target = Vec::with_capacity(3);
    for _ in 0..3 {
        let x = rd_qd(&mut next);
        let y = rd_qd(&mut next);
        target.push(Pt::new(x, y));
    }
    if area2(&target).sign() <= 0 {
        target.reverse();
    }
    // the smallest tile angle has the largest cosine
    let mut cos_min = corners[0].cs;
    for c in corners.iter() {
        if c.cs > cos_min {
            cos_min = c.cs;
        }
    }
    Instance { n, corners, target, area2_tile, cos_min }
}

// ------------------------------------------------------------------ geometry ---

/// Exact rational square root of a `Qd` that must be a rational square. `None` if not.
fn sqrt_rational(v: Qd) -> Option<Qd> {
    if v.q != 0 || v.sign() < 0 {
        return None;
    }
    // v = p/d ; want sqrt(p*d)/d
    let pd = v.p.checked_mul(v.d)?;
    let r = isqrt(pd);
    if r * r != pd {
        return None;
    }
    Some(Qd::new(r, 0, v.d))
}

fn isqrt(n: i128) -> i128 {
    if n < 0 {
        return -1;
    }
    let mut x = (n as f64).sqrt() as i128;
    while x > 0 && x * x > n {
        x -= 1;
    }
    while (x + 1) * (x + 1) <= n {
        x += 1;
    }
    x
}

/// Unit vector along `p -> q`; requires the edge length to be rational (it is, in these targets).
fn unit(p: Pt, q: Pt) -> Option<Pt> {
    let d = q.sub(p);
    let l2 = d.x.mul(d.x).add(d.y.mul(d.y));
    let l = sqrt_rational(l2)?;
    let inv = Qd::new(l.d, 0, l.p); // 1/l
    Some(Pt::new(d.x.mul(inv), d.y.mul(inv)))
}

/// Exact rational length of an edge, or `None` when it is irrational.
fn edge_len(p: Pt, q: Pt) -> Option<Qd> {
    let d = q.sub(p);
    sqrt_rational(d.x.mul(d.x).add(d.y.mul(d.y)))
}

fn rot(cs: Qd, sn: Qd, u: Pt) -> Pt {
    Pt::new(u.x.mul(cs).sub(u.y.mul(sn)), u.x.mul(sn).add(u.y.mul(cs)))
}

fn cross2(a: Pt, b: Pt) -> Qd {
    a.x.mul(b.y).sub(a.y.mul(b.x))
}

/// Candidate tile placements at vertex `vi` of `poly`. Mirrors `cengine::placements`.
fn placements(inst: &Instance, poly: &[Pt], vi: usize, out: &mut Vec<[Pt; 3]>) {
    out.clear();
    let n = poly.len();
    let v = poly[vi];
    let nxt = poly[(vi + 1) % n];
    let prv = poly[(vi + n - 1) % n];
    let (u, w) = match (unit(v, nxt), unit(v, prv)) {
        (Some(a), Some(b)) => (a, b),
        _ => return, // irrational boundary edge: refuse to guess (soundness over completeness)
    };
    for ci in 0..3 {
        let c = inst.corners[ci];
        let r = rot(c.cs, c.sn, u);
        if cross2(u, r).sign() < 0 || cross2(r, w).sign() < 0 {
            continue;
        }
        for k in 0..2 {
            let lq = Qd::int(c.l[k]);
            let mq = Qd::int(c.m[k]);
            let p2 = Pt::new(v.x.add(u.x.mul(lq)), v.y.add(u.y.mul(lq)));
            let p3 = Pt::new(v.x.add(r.x.mul(mq)), v.y.add(r.y.mul(mq)));
            let mut tri = [v, p2, p3];
            if area2(&tri).sign() <= 0 {
                tri = [v, p3, p2];
            }
            out.push(tri);
        }
    }
}

/// Axis-aligned bounds of a polygon, computed once per corner scan and reused across the ~36 point
/// tests that containment performs there. Rejecting on the box first is what makes the
/// most-constrained-corner scan affordable.
#[derive(Clone, Copy)]
pub struct Bbox {
    xlo: Qd,
    xhi: Qd,
    ylo: Qd,
    yhi: Qd,
}

fn bbox(poly: &[Pt]) -> Bbox {
    let mut b = Bbox { xlo: poly[0].x, xhi: poly[0].x, ylo: poly[0].y, yhi: poly[0].y };
    for p in poly.iter().skip(1) {
        if p.x < b.xlo { b.xlo = p.x }
        if p.x > b.xhi { b.xhi = p.x }
        if p.y < b.ylo { b.ylo = p.y }
        if p.y > b.yhi { b.yhi = p.y }
    }
    b
}

/// Is the triangle contained in the polygon? Conservative: every triangle vertex must be inside or
/// on the boundary, and every triangle edge midpoint must be inside or on the boundary.
fn contained(poly: &[Pt], bb: &Bbox, tri: &[Pt; 3]) -> bool {
    // cheap box reject before any winding test
    for v in tri.iter() {
        if v.x < bb.xlo || v.x > bb.xhi || v.y < bb.ylo || v.y > bb.yhi {
            return false;
        }
    }
    let inside = |p: Pt| -> bool {
        // winding test on a convex-or-not simple polygon, using the boundary-crossing rule with
        // exact predicates; points on the boundary count as inside.
        let n = poly.len();
        let mut wind = 0i64;
        for i in 0..n {
            let a = poly[i];
            let b = poly[(i + 1) % n];
            if a == p || b == p || strictly_between(p, a, b) {
                return true;
            }
            let ay = a.y.cmp_to(p.y);
            let by = b.y.cmp_to(p.y);
            use std::cmp::Ordering::*;
            if ay != Greater && by == Greater {
                if cross(a, b, p).sign() > 0 {
                    wind += 1;
                }
            } else if ay == Greater && by != Greater {
                if cross(a, b, p).sign() < 0 {
                    wind -= 1;
                }
            }
        }
        wind != 0
    };
    for i in 0..3 {
        if !inside(tri[i]) {
            return false;
        }
        let a = tri[i];
        let b = tri[(i + 1) % 3];
        let mid = Pt::new(a.x.add(b.x).mul(Qd::new(1, 0, 2)), a.y.add(b.y).mul(Qd::new(1, 0, 2)));
        if !inside(mid) {
            return false;
        }
    }
    true
}

type Edge = (Pt, Pt);

/// `poly \ tri` as a list of simple polygons, by boundary algebra: take the polygon's edges and the
/// triangle's edges reversed, split them all at every vertex lying strictly inside, cancel opposite
/// pairs, then stitch the survivors into loops. Exactly the C++ engine's `subtract`.
fn subtract(poly: &[Pt], tri: &[Pt; 3], out: &mut Vec<Vec<Pt>>) -> bool {
    out.clear();
    let mut edges: Vec<Edge> = Vec::new();
    let n = poly.len();
    for i in 0..n {
        edges.push((poly[i], poly[(i + 1) % n]));
    }
    for i in 0..3 {
        edges.push((tri[(i + 1) % 3], tri[i]));
    }
    // split at all points lying strictly inside an edge
    let mut pts: Vec<Pt> = Vec::new();
    for e in &edges {
        pts.push(e.0);
        pts.push(e.1);
    }
    pts.sort();
    pts.dedup();
    let mut split: Vec<Edge> = Vec::new();
    for e in &edges {
        // Only points inside the edge's own bounding box can lie on it. Without this the split
        // scan is O(m^2) exact `strictly_between` tests (six Qd multiplications each) and dominates
        // the whole node.
        let (xlo, xhi) = if e.0.x < e.1.x { (e.0.x, e.1.x) } else { (e.1.x, e.0.x) };
        let (ylo, yhi) = if e.0.y < e.1.y { (e.0.y, e.1.y) } else { (e.1.y, e.0.y) };
        let mut inner: Vec<Pt> = pts
            .iter()
            .cloned()
            .filter(|p| p.x >= xlo && p.x <= xhi && p.y >= ylo && p.y <= yhi)
            .filter(|p| strictly_between(*p, e.0, e.1))
            .collect();
        inner.sort_by(|a, b| {
            dist2(e.0, *a).cmp_to(dist2(e.0, *b))
        });
        let mut cur = e.0;
        for p in inner {
            split.push((cur, p));
            cur = p;
        }
        split.push((cur, e.1));
    }
    // cancel opposite pairs
    let mut cnt: BTreeMap<Edge, i32> = BTreeMap::new();
    let mut order: Vec<Edge> = Vec::new();
    for e in &split {
        let c = cnt.entry(*e).or_insert(0);
        if *c == 0 {
            order.push(*e);
        }
        *c += 1;
    }
    for e in order.clone() {
        let k = *cnt.get(&e).unwrap_or(&0);
        if k == 0 {
            continue;
        }
        let rev = (e.1, e.0);
        let rk = *cnt.get(&rev).unwrap_or(&0);
        let m = k.min(rk);
        if m > 0 {
            cnt.insert(e, k - m);
            cnt.insert(rev, rk - m);
        }
    }
    let mut fin: Vec<Edge> = Vec::new();
    for e in &order {
        for _ in 0..*cnt.get(e).unwrap_or(&0) {
            fin.push(*e);
        }
    }
    if fin.is_empty() {
        return true;
    }
    // stitch loops: from each vertex pick the most clockwise continuation
    let mut outmap: BTreeMap<Pt, Vec<usize>> = BTreeMap::new();
    for (i, e) in fin.iter().enumerate() {
        outmap.entry(e.0).or_default().push(i);
    }
    let mut used = vec![false; fin.len()];
    for si in 0..fin.len() {
        if used[si] {
            continue;
        }
        let mut loop_pts: Vec<Pt> = Vec::new();
        let mut cur = si;
        loop {
            if used[cur] {
                break;
            }
            used[cur] = true;
            loop_pts.push(fin[cur].0);
            let head = fin[cur].1;
            let incoming = fin[cur].0.sub(head); // reversed direction
            let outs = match outmap.get(&head) {
                Some(v) => v.clone(),
                None => break,
            };
            let mut best: Option<usize> = None;
            for &j in &outs {
                if used[j] {
                    continue;
                }
                let d = fin[j].1.sub(head);
                best = Some(match best {
                    None => j,
                    Some(bj) => {
                        let bd = fin[bj].1.sub(head);
                        if more_clockwise(incoming, d, bd) {
                            j
                        } else {
                            bj
                        }
                    }
                });
            }
            match best {
                Some(j) => cur = j,
                None => break,
            }
            if fin[cur].0 == fin[si].0 && loop_pts.len() >= 3 {
                // closing handled by the used[] check at loop top
            }
        }
        if loop_pts.len() >= 3 {
            let mut lp = loop_pts;
            if area2(&lp).sign() < 0 {
                lp.reverse();
            }
            if area2(&lp).sign() != 0 {
                out.push(lp);
            }
        }
    }
    true
}

/// Is direction `a` more clockwise than `b`, measured from the reference direction `refd`?
fn more_clockwise(refd: Pt, a: Pt, b: Pt) -> bool {
    let sec = |d: Pt| -> i32 {
        let c = cross2(refd, d).sign();
        let dot = refd.x.mul(d.x).add(refd.y.mul(d.y)).sign();
        match (c, dot) {
            (0, s) if s > 0 => 0,
            (x, _) if x < 0 => 1,
            (0, _) => 2,
            _ => 3,
        }
    };
    let (sa, sb) = (sec(a), sec(b));
    if sa != sb {
        return sa < sb;
    }
    cross2(a, b).sign() < 0
}

// -------------------------------------------------------------------- search ---

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % (n.max(1) as u64)) as usize
    }
}

/// Luby sequence: 1,1,2,1,1,2,4,1,... — optimal for unknown runtime distributions.
/// Iterative: if `x = 2^k − 1` the term is `2^(k−1)`, otherwise strip the largest such prefix.
fn luby(i: u64) -> u64 {
    let mut x = i + 1;
    loop {
        let mut k = 1u64;
        while (1u64 << k) - 1 < x {
            k += 1;
        }
        if (1u64 << k) - 1 == x {
            return 1u64 << (k - 1);
        }
        x -= (1u64 << (k - 1)) - 1;
    }
}

struct Search<'a> {
    inst: &'a Instance,
    budget: u64,
    nodes: u64,
    rng: Rng,
    stop: &'a AtomicBool,
    total: &'a AtomicU64,
    shuffle: bool,
}

impl<'a> Search<'a> {
    fn dfs(&mut self, polys: &mut Vec<Vec<Pt>>, left: usize, placed: &mut Vec<[Pt; 3]>) -> bool {
        if self.nodes >= self.budget || self.stop.load(Ordering::Relaxed) {
            return false;
        }
        self.nodes += 1;
        if self.nodes & 0xFFFF == 0 {
            self.total.fetch_add(0x10000, Ordering::Relaxed);
        }
        if polys.is_empty() {
            return left == 0;
        }
        if left == 0 {
            return false;
        }
        // area check: total remaining area must equal `left` tiles exactly
        let mut tot = Qd::zero();
        for p in polys.iter() {
            tot = tot.add(area2(p));
        }
        let need = self.inst.area2_tile.mul(Qd::int(left as i128));
        if tot != need {
            return false;
        }
        // ---- corner selection -------------------------------------------------------------
        // Correctness needs only SOME convex corner: a tile covering a convex corner must have a
        // vertex there (covering it mid-edge would make the tile locally a half-plane, which cannot
        // sit inside a wedge of angle < pi). The engine always takes the lexicographically least
        // vertex. We are therefore free to take the MOST CONSTRAINED one instead (fail-first,
        // Haralick & Elliott 1980), which converts a dead end into an immediate refutation rather
        // than one discovered after descending. Two consequences fall out for free:
        //   * a convex corner with NO legal placement prunes the node at once;
        //   * a corner with exactly ONE placement is forced, and is taken without branching.
        let mut best: Option<(usize, usize, Vec<[Pt; 3]>)> = None;
        let mut buf: Vec<[Pt; 3]> = Vec::with_capacity(6);
        'outer: for (i, p) in polys.iter().enumerate() {
            let n = p.len();
            let bb = bbox(p);
            for vi in 0..n {
                // convex vertices only (CCW polygon => positive turn)
                let prv = p[(vi + n - 1) % n];
                let cur = p[vi];
                let nxt = p[(vi + 1) % n];
                if cross(prv, cur, nxt).sign() <= 0 {
                    continue;
                }
                // Cheap necessary test before any placement geometry: the interior angle must be at
                // least the smallest tile angle. With U = nxt-cur, W = prv-cur and |U|,|W| rational,
                // angle < alpha  <=>  U.W > cos(alpha)*|U||W|, which is exact and needs no
                // containment test at all.
                if let (Some(lu), Some(lw)) = (edge_len(cur, nxt), edge_len(cur, prv)) {
                    let uu = nxt.sub(cur);
                    let ww = prv.sub(cur);
                    let dot = uu.x.mul(ww.x).add(uu.y.mul(ww.y));
                    let rhs = self.inst.cos_min.mul(lu).mul(lw);
                    if dot.sub(rhs).sign() > 0 {
                        return false; // corner too sharp for any tile: node refuted
                    }
                }
                placements(self.inst, p, vi, &mut buf);
                buf.retain(|t| contained(p, &bb, t));
                let k = buf.len();
                if k == 0 {
                    return false; // dead corner: this whole subtree is refuted here
                }
                let better = match &best {
                    None => true,
                    Some((_, _, bc)) => k < bc.len(),
                };
                if better {
                    best = Some((i, vi, buf.clone()));
                    // Stop as soon as the corner is constrained enough to branch on. k == 1 is a
                    // forced move and cannot be improved; k == 2 is already tight, and scanning the
                    // remaining corners to maybe find another 2 costs more than it saves -- the
                    // scan is ~36n^2 exact point tests per node. Correctness is unaffected: ANY
                    // convex corner is a legal anchor.
                    if k <= 2 {
                        break 'outer;
                    }
                }
            }
        }
        let (bi, _bv, mut cands) = match best {
            Some(v) => v,
            None => return false, // no convex corner anywhere: not completable
        };
        let poly = polys[bi].clone();
        // randomized order — the whole point of the restart portfolio.
        // FINDER_SHUFFLE=0 disables it, which recovers the engine's deterministic order and is the
        // control that separates "randomisation hurts" from "the search is wrong".
        if self.shuffle {
            for i in (1..cands.len()).rev() {
                let j = self.rng.below(i + 1);
                cands.swap(i, j);
            }
        }
        for tri in cands {
            let mut pieces: Vec<Vec<Pt>> = Vec::new();
            if !subtract(&poly, &tri, &mut pieces) {
                continue;
            }
            // splice in place: swap_remove the consumed component, append the pieces, then undo.
            // (Cloning the whole region per candidate dominated the runtime.)
            let displaced = polys.swap_remove(bi);
            let base = polys.len();
            let added = pieces.len();
            polys.extend(pieces);
            placed.push(tri);
            let hit = self.dfs(polys, left - 1, placed);
            if hit {
                return true; // keep `placed`: it is the answer
            }
            placed.pop();
            polys.truncate(base);
            polys.push(displaced);
            let last = polys.len() - 1;
            polys.swap(bi, last);
            let _ = added;
            if self.nodes >= self.budget || self.stop.load(Ordering::Relaxed) {
                return false;
            }
        }
        false
    }
}

// -------------------------------------------------------------- verification ---

/// Re-verify a candidate tiling from scratch. This is what makes the finder safe to trust.
fn verify(inst: &Instance, tiles: &[[Pt; 3]]) -> Result<(), String> {
    if tiles.len() != inst.n {
        return Err(format!("tile count {} != N {}", tiles.len(), inst.n));
    }
    // (1) congruence: squared side multiset equal for all tiles
    let key = |t: &[Pt; 3]| {
        let mut s = [dist2(t[0], t[1]), dist2(t[1], t[2]), dist2(t[2], t[0])];
        s.sort();
        s
    };
    let k0 = key(&tiles[0]);
    for t in tiles {
        if key(t) != k0 {
            return Err("tiles not mutually congruent".into());
        }
    }
    // (2) area identity: sum of tile areas equals the target's
    let mut s = Qd::zero();
    for t in tiles {
        let a = area2(t);
        if a.sign() <= 0 {
            return Err("degenerate or clockwise tile".into());
        }
        s = s.add(a);
    }
    if s != area2(&inst.target) {
        return Err("areas do not sum to the target".into());
    }
    if inst.area2_tile.mul(Qd::int(inst.n as i128)) != s {
        return Err("tile area x N != total".into());
    }
    // (3) disjointness + coverage: subtract every tile from the target and require nothing left
    let mut region: Vec<Vec<Pt>> = vec![inst.target.clone()];
    for t in tiles {
        let mut done = false;
        for i in 0..region.len() {
            let bb = bbox(&region[i]);
            if contained(&region[i], &bb, t) {
                let poly = region[i].clone();
                let mut pieces = Vec::new();
                if subtract(&poly, t, &mut pieces) {
                    region.remove(i);
                    region.extend(pieces);
                    done = true;
                    break;
                }
            }
        }
        if !done {
            return Err("a tile is not contained in the remaining region".into());
        }
    }
    if !region.is_empty() {
        return Err(format!("{} uncovered piece(s) remain", region.len()));
    }
    Ok(())
}

fn fmt_qd(v: Qd) -> String {
    format!("{} {} {}", v.p, v.q, v.d)
}

// ---------------------------------------------------------------------- main ---

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: finder <instance.txt> [threads] [seed]");
        eprintln!("  sound but incomplete: a reported tiling is re-verified; finding nothing proves nothing");
        process::exit(1);
    }
    let path = args[1].clone();
    let threads: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(8);
    let seed0: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(0x9E3779B97F4A7C15);
    let shuffle_on = env::var("FINDER_SHUFFLE").map(|v| v != "0").unwrap_or(true);
    let inst = parse_instance(&path);
    println!(
        "instance {} : N={} D={} threads={} shuffle={} (Luby restarts)",
        path,
        inst.n,
        d_val(),
        threads,
        shuffle_on
    );

    let stop = Arc::new(AtomicBool::new(false));
    let total = Arc::new(AtomicU64::new(0));
    let restarts = Arc::new(AtomicU64::new(0));
    let found: Arc<Mutex<Option<Vec<[Pt; 3]>>>> = Arc::new(Mutex::new(None));
    let t0 = Instant::now();

    let mut handles = Vec::new();
    for tid in 0..threads {
        let inst = inst.clone();
        let shuffle_on = shuffle_on;
        let stop = stop.clone();
        let total = total.clone();
        let restarts = restarts.clone();
        let found = found.clone();
        handles.push(std::thread::spawn(move || {
            let mut r = 0u64;
            let unit_budget = 20_000u64;
            while !stop.load(Ordering::Relaxed) {
                let budget = if shuffle_on { luby(r) * unit_budget } else { u64::MAX };
                let mut s = Search {
                    inst: &inst,
                    budget,
                    nodes: 0,
                    rng: Rng(seed0 ^ ((tid as u64) << 32) ^ (r.wrapping_mul(0x100000001B3))),
                    stop: &stop,
                    total: &total,
                    shuffle: shuffle_on,
                };
                let mut polys = vec![inst.target.clone()];
                let mut placed: Vec<[Pt; 3]> = Vec::new();
                let ok = s.dfs(&mut polys, inst.n, &mut placed);
                total.fetch_add(s.nodes & 0xFFFF, Ordering::Relaxed); // the rest was streamed
                restarts.fetch_add(1, Ordering::Relaxed);
                if ok {
                    *found.lock().unwrap() = Some(placed);
                    stop.store(true, Ordering::Relaxed);
                    return;
                }
                r += 1;
            }
        }));
    }
    // progress
    let stop_p = stop.clone();
    let total_p = total.clone();
    let restarts_p = restarts.clone();
    let reporter = std::thread::spawn(move || {
        let mut last = 0u64;
        while !stop_p.load(Ordering::Relaxed) {
            std::thread::sleep(std::time::Duration::from_secs(15));
            if stop_p.load(Ordering::Relaxed) {
                break;
            }
            let n = total_p.load(Ordering::Relaxed);
            let rs = restarts_p.load(Ordering::Relaxed);
            let el = t0.elapsed().as_secs_f64();
            println!(
                "  nodes {:>12}  restarts {:>7}  {:>8.0} nodes/s  t={:.0}s",
                n,
                rs,
                (n - last) as f64 / 15.0,
                el
            );
            last = n;
        }
    });
    for h in handles {
        let _ = h.join();
    }
    stop.store(true, Ordering::Relaxed);
    let _ = reporter.join();

    let g = found.lock().unwrap();
    match &*g {
        Some(tiles) => {
            println!(
                "RESULT FOUND_TILING nodes={} restarts={} t={:.1}s",
                total.load(Ordering::Relaxed),
                restarts.load(Ordering::Relaxed),
                t0.elapsed().as_secs_f64()
            );
            match verify(&inst, tiles) {
                Ok(()) => {
                    println!("VERIFIED ok: {} congruent tiles, exact areas, no overlap, no gap", tiles.len());
                    for t in tiles.iter() {
                        println!(
                            "TILE {} {} {} {} {} {}",
                            fmt_qd(t[0].x), fmt_qd(t[0].y),
                            fmt_qd(t[1].x), fmt_qd(t[1].y),
                            fmt_qd(t[2].x), fmt_qd(t[2].y)
                        );
                    }
                }
                Err(e) => {
                    println!("VERIFICATION FAILED: {e}");
                    println!("(the candidate is rejected; this is a finder bug, not a theorem)");
                    process::exit(2);
                }
            }
        }
        None => {
            println!(
                "RESULT NO_TILING_FOUND nodes={} restarts={} t={:.1}s  (proves nothing: the finder is incomplete)",
                total.load(Ordering::Relaxed),
                restarts.load(Ordering::Relaxed),
                t0.elapsed().as_secs_f64()
            );
        }
    }
}
