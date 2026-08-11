// Realizability screen for the frontier band: which N are settled by a closed form,
// and which are left to the engine.  Mirrors the criteria of code/verify_frontier.py.

fn isqrt(n: u64) -> u64 { (n as f64).sqrt() as u64 }
fn issq(n: u64) -> bool { let r = isqrt(n); (r.saturating_sub(1)..=r + 1).any(|k| k * k == n) }

/// N is a sum of two positive squares.
fn sum2sq(n: u64) -> Option<(u64, u64)> {
    for e in 1..=isqrt(n) {
        if issq(n - e * e) { return Some((e, isqrt(n - e * e))); }
    }
    None
}

/// Commensurable-angle realizability [Beeson, "Seven-triangle", Thm 3]:
/// N a square, a sum of two squares, or 2,3,6 times a square.
fn commensurable(n: u64) -> Option<String> {
    if issq(n) { return Some(format!("{}^2", isqrt(n))); }
    if let Some((a, b)) = sum2sq(n) { return Some(format!("{}^2+{}^2", a, b)); }
    for k in [2u64, 3, 6] {
        if n % k == 0 && issq(n / k) { return Some(format!("{}*{}^2", k, isqrt(n / k))); }
    }
    None
}

fn main() {
    let lo: u64 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(81);
    let hi: u64 = std::env::args().nth(2).and_then(|s| s.parse().ok()).unwrap_or(90);
    println!("{:>4}  {:<12} {:<18} {}", "N", "verdict", "witness", "note");
    for n in lo..=hi {
        match commensurable(n) {
            Some(w) => println!("{:>4}  {:<12} {:<18} realizable by the commensurable construction", n, "REALIZABLE", w),
            None => {
                let sqfree = (2..=isqrt(n)).all(|p| n % (p * p) != 0);
                let prime = n > 1 && (2..=isqrt(n)).all(|p| n % p != 0);
                let note = if prime {
                    format!("prime; {} mod 12 = {}", n, n % 12)
                } else if sqfree {
                    "squarefree: gamma=2alpha branch dead by N-form".to_string()
                } else {
                    "not squarefree: gamma=2alpha branch alive -> engine".to_string()
                };
                println!("{:>4}  {:<12} {:<18} {}", n, "not by form", "-", note);
            }
        }
    }
}
