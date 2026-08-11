// How much of the pentagon lemma's stub machinery is actually needed?
// The lemma sends a stub walking by e^2 (mod b) until it lands in a gap of <a,b,c>.
// Question: are the stubs gaps ALREADY, so that no walk ever happens?
fn gcd(mut x: u128, mut y: u128) -> u128 { while y != 0 { let t = x % y; x = y; y = t; } x }

fn in_semigroup(t: u128, a: u128, b: u128, c: u128) -> bool {
    let mut z = 0;
    while z * c <= t {
        let r1 = t - z * c;
        let mut y = 0;
        while y * b <= r1 {
            if (r1 - y * b) % a == 0 { return true; }
            y += 1;
        }
        z += 1;
    }
    false
}

fn main() {
    let fmax: u128 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(80);
    let (mut members, mut all_gap) = (0u64, 0u64);
    let mut worst_step = 0u128;
    let mut examples: Vec<String> = Vec::new();
    for f in 2..=fmax {
        for e in 1..f {
            if gcd(e, f) != 1 { continue; }
            let (a, b, c) = (e * f, f * f - e * e, f * f);
            members += 1;
            let s0 = [(e * e) % b, if a > b { a - b } else { b - a }];
            let mut every_stub_is_gap = true;
            let mut first_gap_step = 0u128;
            for &start in s0.iter() {
                let mut s = start;
                let mut k = 0u128;
                loop {
                    let is_gap = s != 0 && !in_semigroup(s, a, b, c);
                    if k == 0 && !is_gap { every_stub_is_gap = false; }
                    if is_gap { if k > first_gap_step { first_gap_step = k; } break; }
                    k += 1;
                    if k > e + 2 { first_gap_step = u128::MAX; break; }
                    s = (s + e * e) % b;
                }
            }
            if every_stub_is_gap { all_gap += 1; }
            else if examples.len() < 8 {
                examples.push(format!("(e,f)=({},{}) tile=({},{},{}) stubs={:?}", e, f, a, b, c, s0));
            }
            if first_gap_step != u128::MAX && first_gap_step > worst_step { worst_step = first_gap_step; }
        }
    }
    println!("members tested (f <= {}): {}", fmax, members);
    println!("members where BOTH initial stubs are already gaps (no walk needed): {}", all_gap);
    println!("members needing at least one walk step: {}", members - all_gap);
    println!("max walk steps ever needed: {}", worst_step);
    for ex in &examples { println!("   needs a walk: {}", ex); }
}
