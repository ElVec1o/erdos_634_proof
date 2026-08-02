//! cert.rs — Lean kernel-certificate generation, ported from gencert.py / gencert_quad.py.
//!
//! Reads an engine instance file (target polygon, tile, D) and its witness tiling, verifies all
//! four conditions exactly in Z[sqrt D] after clearing denominators, then emits a zero-axiom
//! Lean file whose `decide` re-runs the same checks in the kernel.
//!
//!   C1  every tile's squared side multiset = (scale·(a,b,c))², all rational
//!   C2  CCW orientation + every vertex inside the closed target (one half-plane per edge)
//!   C3  an explicit separating edge-line for each of the N(N−1)/2 pairs => disjoint interiors
//!   C4  signed 2-areas sum to the target's
//!
//! Handles triangle and quadrilateral targets uniformly (the `POLY k` extension).

use crate::alg::{cross, dist2, Alg, Pt, Rat, Tri};
use std::fs;

fn lcm(a: i128, b: i128) -> i128 {
    fn g(mut a: i128, mut b: i128) -> i128 {
        while b != 0 {
            let t = a % b;
            a = b;
            b = t;
        }
        a.abs().max(1)
    }
    (a / g(a, b)).abs() * b.abs()
}

pub struct Instance {
    pub d: i128,
    pub abc: [i128; 3],
    pub n: i128,
    pub target: Vec<Pt>,
}

/// tokens: D | a b c | 3×(cos,sin as p q r ×2) | area2 (p q r) | N | [POLY k] | k×(x,y)
pub fn parse_instance(path: &str) -> Instance {
    let txt = fs::read_to_string(path).expect("read instance");
    let mut it = txt.split_whitespace().peekable();
    let mut next = || -> String { it.next().expect("truncated instance").to_string() };
    let d: i128 = next().parse().unwrap();
    let abc = [
        next().parse::<i128>().unwrap(),
        next().parse::<i128>().unwrap(),
        next().parse::<i128>().unwrap(),
    ];
    // 3 corners × (cos, sin), then area2 — 7 QD triples, skipped: only the target is needed here
    for _ in 0..7 {
        let _ = (next(), next(), next());
    }
    let n: i128 = next().parse().unwrap();
    let mut k = 3usize;
    // optional POLY marker
    let tok = next();
    let first_after: Option<String>;
    if tok == "POLY" {
        k = next().parse::<usize>().unwrap();
        first_after = None;
    } else {
        first_after = Some(tok);
    }
    let mut nums: Vec<i128> = Vec::new();
    if let Some(t) = first_after {
        nums.push(t.parse().unwrap());
    }
    while nums.len() < 6 * k {
        nums.push(next().parse().unwrap());
    }
    let mut target = Vec::new();
    for i in 0..k {
        let s = &nums[6 * i..6 * i + 6];
        target.push(Pt {
            x: Alg { a: Rat::new(s[0], s[2]), b: Rat::new(s[1], s[2]) },
            y: Alg { a: Rat::new(s[3], s[5]), b: Rat::new(s[4], s[5]) },
        });
    }
    Instance { d, abc, n, target }
}

pub fn parse_witness(path: &str) -> Vec<Tri> {
    let txt = fs::read_to_string(path).expect("read witness");
    let mut out = Vec::new();
    for line in txt.lines().skip(1) {
        let tk: Vec<i128> = line.split_whitespace().filter_map(|s| s.parse().ok()).collect();
        if tk.len() != 18 {
            continue;
        }
        let mut vs = [Pt { x: Alg::ZERO, y: Alg::ZERO }; 3];
        for k in 0..3 {
            let s = &tk[6 * k..6 * k + 6];
            vs[k] = Pt {
                x: Alg { a: Rat::new(s[0], s[2]), b: Rat::new(s[1], s[2]) },
                y: Alg { a: Rat::new(s[3], s[5]), b: Rat::new(s[4], s[5]) },
            };
        }
        out.push(vs);
    }
    out
}

fn denoms(p: &Pt, acc: &mut i128) {
    *acc = lcm(*acc, p.x.a.d);
    *acc = lcm(*acc, p.x.b.d);
    *acc = lcm(*acc, p.y.a.d);
    *acc = lcm(*acc, p.y.b.d);
}

fn scale_pt(p: &Pt, s: i128) -> [i128; 4] {
    let f = Rat::int(s);
    let (xa, xb, ya, yb) = (p.x.a.mul(f), p.x.b.mul(f), p.y.a.mul(f), p.y.b.mul(f));
    for r in [xa, xb, ya, yb] {
        assert_eq!(r.d, 1, "scale {s} does not clear denominators");
    }
    [xa.n, xb.n, ya.n, yb.n]
}

/// full pipeline: verify exactly, then emit the Lean certificate
pub fn generate(inst_path: &str, wit_path: &str, out_path: &str, ns: &str) -> Result<(), String> {
    let inst = parse_instance(inst_path);
    let mut tiles = parse_witness(wit_path);
    let d = inst.d;
    if tiles.len() as i128 != inst.n {
        return Err(format!("witness has {} tiles, instance says {}", tiles.len(), inst.n));
    }
    // clearing scale over tiles and target
    let mut s: i128 = 1;
    for t in &tiles {
        for p in t.iter() {
            denoms(p, &mut s);
        }
    }
    for p in &inst.target {
        denoms(p, &mut s);
    }
    // orient CCW
    for t in tiles.iter_mut() {
        if cross(t[0], t[1], t[2], d).sgn(d) < 0 {
            t.swap(1, 2);
        }
    }
    // C1
    let mut sq: Vec<i128> = inst.abc.iter().map(|x| (x * s) * (x * s)).collect();
    sq.sort();
    for (i, t) in tiles.iter().enumerate() {
        let mut ds: Vec<i128> = Vec::new();
        for k in 0..3 {
            let dd = dist2(t[k], t[(k + 1) % 3], d);
            if !dd.b.is_zero() {
                return Err(format!("C1 tile {i}: irrational side²"));
            }
            let v = dd.a.mul(Rat::int(s)).mul(Rat::int(s));
            if v.d != 1 {
                return Err(format!("C1 tile {i}: non-integral scaled side²"));
            }
            ds.push(v.n);
        }
        ds.sort();
        if ds != sq {
            return Err(format!("C1 tile {i}: {ds:?} != {sq:?}"));
        }
    }
    // C2
    let k = inst.target.len();
    for (i, t) in tiles.iter().enumerate() {
        for v in t.iter() {
            for e in 0..k {
                if cross(inst.target[e], inst.target[(e + 1) % k], *v, d).sgn(d) < 0 {
                    return Err(format!("C2 tile {i}: vertex outside target"));
                }
            }
        }
    }
    // C4
    let mut tot = Alg::ZERO;
    for t in &tiles {
        tot = tot.add(cross(t[0], t[1], t[2], d));
    }
    let mut ta = Alg::ZERO;
    for i in 1..k - 1 {
        ta = ta.add(cross(inst.target[0], inst.target[i], inst.target[i + 1], d));
    }
    if tot != ta {
        return Err("C4 area mismatch".into());
    }
    let area2 = {
        let v = [ta.a.mul(Rat::int(s)).mul(Rat::int(s)), ta.b.mul(Rat::int(s)).mul(Rat::int(s))];
        assert!(v[0].d == 1 && v[1].d == 1);
        [v[0].n, v[1].n]
    };
    // C3 separators
    let n = tiles.len();
    let mut wit: Vec<(bool, usize)> = Vec::with_capacity(n * (n - 1) / 2);
    for i in 0..n {
        for j in (i + 1)..n {
            let (aa, bb) = (&tiles[i], &tiles[j]);
            let mut found = None;
            'search: for (flip, src) in [(true, aa), (false, bb)] {
                for e in 0..3 {
                    let (p, q) = (src[e], src[(e + 1) % 3]);
                    let sa: Vec<i32> = aa.iter().map(|v| cross(p, q, *v, d).sgn(d)).collect();
                    let sb: Vec<i32> = bb.iter().map(|v| cross(p, q, *v, d).sgn(d)).collect();
                    let an = sa.iter().all(|&x| x >= 0);
                    let ap = sa.iter().all(|&x| x <= 0);
                    let bn = sb.iter().all(|&x| x >= 0);
                    let bp = sb.iter().all(|&x| x <= 0);
                    if (an && bp) || (ap && bn) {
                        found = Some((flip, e));
                        break 'search;
                    }
                }
            }
            match found {
                Some(w) => wit.push(w),
                None => return Err(format!("C3 no separator for pair {i},{j}")),
            }
        }
    }
    // ---- emit ----
    let tile_lines: Vec<String> = tiles
        .iter()
        .map(|t| {
            let v: Vec<String> = t
                .iter()
                .map(|p| {
                    let q = scale_pt(p, s);
                    format!("({},{},{},{})", q[0], q[1], q[2], q[3])
                })
                .collect();
            format!("  ({})", v.join(", "))
        })
        .collect();
    let mut wit_lines: Vec<String> = Vec::new();
    for chunk in wit.chunks(12) {
        let c: Vec<String> = chunk
            .iter()
            .map(|(f, e)| format!("({},{})", if *f { "true" } else { "false" }, e))
            .collect();
        wit_lines.push(format!("  {}", c.join(", ")));
    }
    let qdefs: Vec<String> = inst
        .target
        .iter()
        .enumerate()
        .map(|(i, p)| {
            let q = scale_pt(p, s);
            format!("def q{} : Pt := ({},{},{},{})", i + 1, q[0], q[1], q[2], q[3])
        })
        .collect();
    let inside: Vec<String> = (0..k)
        .map(|i| format!("znonneg (cross q{} q{} v)", i + 1, (i + 1) % k + 1))
        .collect();
    let sqset: Vec<String> = sq.iter().map(|q| format!("s.contains (({q}:Int),(0:Int))")).collect();
    let lean = format!(
        r#"-- {out} — zero-axiom kernel verification of a tiling certificate (Erdos #634).
-- {n} copies of the tile {abc:?} tile the target of {inst_path}, coordinates scaled by {s}
-- into Z[sqrt{d}]. Kernel checks: (C1) squared side multiset {sq:?}; (C2) CCW + vertices in the
-- closed target ({k} half-planes); (C3) an explicit separating edge-line per pair ({np} pairs)
-- => disjoint interiors; (C4) signed 2-areas sum to the target's. Generated by rust/tiler
-- (`tiler cert`), which re-checks all four exactly in Z[sqrt{d}] before emitting. No imports,
-- no axioms.
namespace {ns}
abbrev ZD := Int × Int
abbrev Pt := Int × Int × Int × Int
def zmul (u v : ZD) : ZD := (u.1*v.1 + {d}*u.2*v.2, u.1*v.2 + u.2*v.1)
def zsub (u v : ZD) : ZD := (u.1 - v.1, u.2 - v.2)
def zadd (u v : ZD) : ZD := (u.1 + v.1, u.2 + v.2)
def znonneg (z : ZD) : Bool :=
  if 0 <= z.1 then (if 0 <= z.2 then true else {d}*z.2*z.2 <= z.1*z.1)
  else (if z.2 < 0 then false else z.1*z.1 <= {d}*z.2*z.2)
def znonpos (z : ZD) : Bool := znonneg (-z.1, -z.2)
def zpos (z : ZD) : Bool := !(znonpos z)
def px (p : Pt) : ZD := (p.1, p.2.1)
def py (p : Pt) : ZD := (p.2.2.1, p.2.2.2)
def cross (o a b : Pt) : ZD :=
  zsub (zmul (zsub (px a) (px o)) (zsub (py b) (py o))) (zmul (zsub (py a) (py o)) (zsub (px b) (px o)))
def dist2 (p q : Pt) : ZD :=
  zadd (zmul (zsub (px q) (px p)) (zsub (px q) (px p))) (zmul (zsub (py q) (py p)) (zsub (py q) (py p)))
abbrev Tri := Pt × Pt × Pt
def t1 (t : Tri) : Pt := t.1
def t2 (t : Tri) : Pt := t.2.1
def t3 (t : Tri) : Pt := t.2.2
def congOK (t : Tri) : Bool :=
  let d1 := dist2 (t1 t) (t2 t); let d2 := dist2 (t2 t) (t3 t); let d3 := dist2 (t3 t) (t1 t)
  let s : List ZD := [d1, d2, d3]
  {sqset}
  && d1.2 == 0 && d2.2 == 0 && d3.2 == 0 && (d1.1 + d2.1 + d3.1 == {sqsum})
{qdefs}
def insideOK (t : Tri) : Bool :=
  zpos (cross (t1 t) (t2 t) (t3 t)) &&
  [t1 t, t2 t, t3 t].all (fun v => {inside})
def sepBy (P Q : Pt) (A B : Tri) : Bool :=
  let sA := [t1 A, t2 A, t3 A].map (fun v => cross P Q v)
  let sB := [t1 B, t2 B, t3 B].map (fun v => cross P Q v)
  (sA.all znonneg && sB.all znonpos) || (sA.all znonpos && sB.all znonneg)
def edgeOf (t : Tri) (e : Nat) : Pt × Pt :=
  if e == 0 then (t1 t, t2 t) else if e == 1 then (t2 t, t3 t) else (t3 t, t1 t)
def area2 (t : Tri) : ZD := cross (t1 t) (t2 t) (t3 t)
def area2target : ZD := (({a0}:Int), ({a1}:Int))
def tiles : List Tri := [
{tls}
]
def wit : List (Bool × Nat) := [
{wts}
]
def pairSep (A B : Tri) (w : Bool × Nat) : Bool :=
  let pq := edgeOf (if w.1 then A else B) w.2
  sepBy pq.1 pq.2 A B
def checkPairs : List Tri → List (Bool × Nat) → Bool
  | [], ws => ws.isEmpty
  | t :: rest, ws =>
      let n := rest.length
      (ws.take n).length == n
      && (List.zip rest (ws.take n)).all (fun (u, w) => pairSep t u w)
      && checkPairs rest (ws.drop n)
def zsum (l : List ZD) : ZD := l.foldl zadd ((0:Int),(0:Int))
def checkAll : Bool :=
  tiles.length == {n} && tiles.all congOK && tiles.all insideOK
  && checkPairs tiles wit && zsum (tiles.map area2) == area2target
set_option maxRecDepth {mrd} in
set_option maxHeartbeats 0 in
theorem {lns}_certificate : checkAll = true := by decide
end {ns}
"#,
        out = out_path,
        n = n,
        abc = inst.abc,
        inst_path = inst_path,
        s = s,
        d = d,
        sq = sq,
        k = k,
        np = wit.len(),
        ns = ns,
        sqset = sqset.join(" && "),
        sqsum = sq.iter().sum::<i128>(),
        qdefs = qdefs.join("\n"),
        inside = inside.join(" && "),
        a0 = area2[0],
        a1 = area2[1],
        tls = tile_lines.join(",\n"),
        wts = wit_lines.join(",\n"),
        mrd = (128 * n).max(8192),
        lns = ns.to_lowercase(),
    );
    fs::write(out_path, lean).map_err(|e| e.to_string())?;
    println!(
        "  C1..C4 verified exactly; scale {s}, {np} separators; wrote {out_path}",
        s = s,
        np = wit.len()
    );
    Ok(())
}
