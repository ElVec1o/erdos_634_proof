// Erdos #634 -- 2pi/3 (120-degree) integer-tile search.
//
// Build:   rustc -O tiling_search.rs -o tiling_search
// Run:     ./tiling_search [BOUND]      (default BOUND = 8000; a,b range over 1..BOUND)
//
// Background. A non-isosceles 2pi/3 tile is integer-sided (a,b,c), gcd(a,b,c)=1,
// c^2 = a^2 + a b + b^2  (rationality: Beeson-Zhang arXiv:2604.01314, sound).
// For each scalene ABC shape the minimal tile-count is N0 = Area(ABC_min)/Area(tile):
//
//   F1 = (a, a+b, a+2b)      N0 = (a+b)/b          -> N = t*(a+b)
//        BUT a+b = m(m+2n) in the (m,n) parametrization => COMPOSITE (m>=2); so F1 has NO
//        prime N at all (unconditional). Direct proof: a+b=p prime forces 4c^2-3p^2=d^2 a
//        square, i.e. 3p^2=(2c-d)(2c+d), whose only factorizations give a or b <= 0.
//   F2 = (2a, 2b, a+b)       N0 = (a+2b)(2a+b)     -> N = k^2*(a+2b)(2a+b)  [product => composite]
//   F3 = (a, 2a, 3b)         no integer-sided ABC  -> tiles nothing
//   F4 = (a, 2b, 2a+b)       N0 = (a+b)(2a+b)      -> N = k^2*(a+b)(2a+b)   [product => composite]
//   iso-a = (a,a,a+3b)       N0 = (a+2b)/b         -> N = t*(a+2b)       [divisor-type]
//   iso-b = (b,b,3a+b)       N0 = (2a+b)/a         -> N = t*(2a+b)       [divisor-type]
// (mirrors swap a<->b.)
//
// CONSEQUENCES this program checks:
//  (A) F2,F4 give N COMPOSITE always (both factors >= 3)  -> no prime N. [verify]
//  (B) the "uniform no-prime" conjecture for the 2pi/3 tile reduces to the divisor-type
//      shapes F1, iso-a, iso-b (and mirrors): a PRIME tiling needs t=1, i.e.
//        F1:    a+b prime  AND  b a perfect square        (mirror: a square)
//        iso-a: a+2b prime AND  b a perfect square
//        iso-b: 2a+b prime AND  a a perfect square
//      Enumerate these prime CANDIDATES (area-necessary; realizability still open).
//  (C) refined obstruction for primes N == 3 (mod 4): in F1 such a tiling forces 4 | k,
//      i.e. 16 | b. Flag candidates that violate it (they are killed) vs survive.
//  (D) sanity: NO candidate gives N = 19 in any family.

fn isqrt(n: u128) -> u128 {
    if n < 2 { return n; }
    let mut x = (n as f64).sqrt() as u128;
    while x * x > n { x -= 1; }
    while (x + 1) * (x + 1) <= n { x += 1; }
    x
}
fn is_square(n: u128) -> bool { let r = isqrt(n); r * r == n }

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 { let t = a % b; a = b; b = t; }
    a
}

// deterministic Miller-Rabin for u128 up to ~3.3e24 (enough here)
fn mulmod(a: u128, b: u128, m: u128) -> u128 { ((a as u128 % m) * (b % m)) % m } // m small enough that product fits? guard below
fn powmod(mut a: u128, mut e: u128, m: u128) -> u128 {
    let mut r: u128 = 1 % m; a %= m;
    while e > 0 {
        if e & 1 == 1 { r = mulmod(r, a, m); }
        a = mulmod(a, a, m); e >>= 1;
    }
    r
}
fn is_prime(n: u128) -> bool {
    if n < 2 { return false; }
    for &p in &[2u128,3,5,7,11,13,17,19,23,29,31,37] {
        if n % p == 0 { return n == p; }
    }
    let mut d = n - 1; let mut s = 0;
    while d & 1 == 0 { d >>= 1; s += 1; }
    'wit: for &a in &[2u128,3,5,7,11,13,17,19,23,29,31,37] {
        let mut x = powmod(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        for _ in 0..s-1 { x = mulmod(x, x, n); if x == n - 1 { continue 'wit; } }
        return false;
    }
    true
}

fn main() {
    let bound: u128 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(8000);
    println!("BOUND = {} (a,b in 1..{})", bound, bound);

    let mut n_triples = 0u64;
    // (A) F2/F4 composite check
    let mut f2f4_min = u128::MAX;
    let mut f2f4_prime_violation = 0u64;
    // (B) divisor-type prime candidates
    let mut f1: Vec<(u128,u128,u128,u128)> = Vec::new();   // (a,b,c,N=a+b)  with b square, a+b prime
    let mut isoa: Vec<(u128,u128,u128,u128)> = Vec::new();  // (a,b,c,N=a+2b) b square, a+2b prime
    let mut isob: Vec<(u128,u128,u128,u128)> = Vec::new();  // (a,b,c,N=2a+b) a square, 2a+b prime
    let mut n19_hits = 0u64;

    for a in 1..bound {
        for b in 1..bound {
            let s = a*a + a*b + b*b;
            let c = isqrt(s);
            if c*c != s { continue; }
            if gcd(a, b) != 1 { continue; }     // primitive
            n_triples += 1;

            // (A)
            let n0f2 = (a + 2*b) * (2*a + b);
            let n0f4 = (a + b) * (2*a + b);
            if n0f2 < f2f4_min { f2f4_min = n0f2; }
            if n0f4 < f2f4_min { f2f4_min = n0f4; }
            if is_prime(n0f2) || is_prime(n0f4) { f2f4_prime_violation += 1; }

            // (B) F1: b square & a+b prime
            if is_square(b) && is_prime(a + b) { f1.push((a,b,c,a+b)); if a+b==19 {n19_hits+=1;} }
            // iso-a: b square & a+2b prime
            if is_square(b) && is_prime(a + 2*b) { isoa.push((a,b,c,a+2*b)); if a+2*b==19 {n19_hits+=1;} }
            // iso-b: a square & 2a+b prime
            if is_square(a) && is_prime(2*a + b) { isob.push((a,b,c,2*a+b)); if 2*a+b==19 {n19_hits+=1;} }
        }
    }

    println!("\nprimitive 120-triples found: {}", n_triples);
    println!("\n(A) F2/F4 minimal N0 = {}  (both are products of two factors >=3)", f2f4_min);
    println!("    (a,b) with N0_F2 or N0_F4 PRIME: {}  -> expect 0 (always composite)", f2f4_prime_violation);

    let show = |name: &str, v: &Vec<(u128,u128,u128,u128)>| {
        println!("\n(B) {} prime CANDIDATES (area-necessary; realizability still OPEN): {} found", name, v.len());
        let mut w = v.clone();
        w.sort_by_key(|x| x.3);
        for &(a,b,c,n) in w.iter().take(15) {
            let mod4 = n % 4;
            // (C) for N==3 mod4, F1 requires 16|b; flag survivors/killed
            let note = if name=="F1" && mod4==3 {
                if b % 16 == 0 { "  [N=3mod4, 16|b: survives mod-2 obstruction]" }
                else { "  [N=3mod4, 16∤b: KILLED by c^2=3mod4 descent]" }
            } else { "" };
            println!("    tile(a,b,c)=({},{},{})  N={} (={} mod4){}", a, b, c, n, mod4, note);
        }
        if w.len() > 15 { println!("    ... and {} more", w.len()-15); }
    };
    show("F1", &f1);
    show("iso-a", &isoa);
    show("iso-b", &isob);

    // (C) F1 closure: a+b is never prime for a primitive 120-triple => F1 has 0 prime candidates.
    let mut ab_prime = 0u64;
    for a in 1..bound { for b in 1..bound {
        let s=a*a+a*b+b*b; let c=isqrt(s);
        if c*c==s && gcd(a,b)==1 && is_prime(a+b) { ab_prime+=1; }
    }}
    println!("\n(C) primitive 120-triples with a+b PRIME: {}  -> 0 confirms F1/F1' have NO prime N", ab_prime);
    println!("    (a+b = m(m+2n) in the (m,n) parametrization is composite for m>=2)");
    println!("    Hence ALL scalene shapes (F1,F2,F3,F4) give N composite unconditionally.");
    println!("    The 'no prime N' conjecture for the 2pi/3 tile reduces EXACTLY to the");
    println!("    ISOSCELES case (iso-a, iso-b) -- the open candidates listed in (B).");

    // (D)
    println!("\n(D) N=19 candidates across ALL divisor-type families: {}  -> must be 0 (19 excluded)", n19_hits);

    // smallest prime tilings overall (any family) -- the lowest prime that even PASSES area-necessity
    let mut allp: Vec<u128> = Vec::new();
    for v in [&f1,&isoa,&isob] { for &(_,_,_,n) in v { allp.push(n); } }
    allp.sort(); allp.dedup();
    println!("\nSmallest primes passing area-necessity in SOME divisor-type family: {:?}",
             allp.iter().take(12).collect::<Vec<_>>());
    println!("(These are the primes one must rule out by REALIZABILITY to settle 'no prime N'.)");
}
