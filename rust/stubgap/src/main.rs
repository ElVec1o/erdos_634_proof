// Conjecture under test: for the base-beta tile (a,b,c) = (ef, f^2-e^2, f^2) with gcd(e,f)=1,
// 1 <= e < f, the second initial stub |a-b| is a GAP of the numerical semigroup <a,b,c>.
// If true, the pentagon lemma's second-stub branch closes with no iteration at all.
fn gcd(mut x: u128, mut y: u128) -> u128 { while y != 0 { let t = x % y; x = y; y = t; } x }

/// is t representable as x*a + y*b + z*c with x,y,z >= 0 ?
fn in_semigroup(t: u128, a: u128, b: u128, c: u128) -> bool {
    let mut z = 0;
    while z * c <= t {
        let r1 = t - z * c;
        let mut y = 0;
        while y * b <= r1 {
            let r2 = r1 - y * b;
            if r2 % a == 0 { return true; }
            y += 1;
        }
        z += 1;
    }
    false
}

fn main() {
    let fmax: u128 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(120);
    let (mut tested, mut fails) = (0u64, 0u64);
    let mut min_ab_one = 0u64;
    for f in 2..=fmax {
        for e in 1..f {
            if gcd(e, f) != 1 { continue; }
            let (a, b, c) = (e * f, f * f - e * e, f * f);
            let t = if a > b { a - b } else { b - a };
            tested += 1;
            if a.min(b) == 1 { min_ab_one += 1; }
            if t == 0 || in_semigroup(t, a, b, c) {
                fails += 1;
                if fails <= 10 {
                    println!("  COUNTEREXAMPLE (e,f)=({},{})  tile=({},{},{})  |a-b|={}", e, f, a, b, c, t);
                }
            }
        }
    }
    println!("tested {} coprime pairs with f <= {}", tested, fmax);
    println!("pairs with min(a,b) = 1: {}   (the only way the proof could break)", min_ab_one);
    println!("counterexamples: {}", fails);
    println!("{}", if fails == 0 { "CONJECTURE HOLDS on the whole range" } else { "*** REFUTED ***" });
}
