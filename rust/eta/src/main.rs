// ETA for a running cengine parallel search.
//
// The engine terminates when g_qhead >= g_queue.size(); the progress line prints
//   "par nodes~N  leaves L  queue HEAD/TOTAL  threads T  t=SECS"
// so true progress is HEAD/TOTAL -- but TOTAL grows as hard subtrees split.  We therefore
// fit both HEAD(t) and TOTAL(t) over the recent window and solve for their crossing, which
// is the only honest way to get a finish time out of a growing work list.
//
// Reports a range, not a point: the crossing from the recent window, and a slower bound
// from the whole-run average, because these searches are wildly non-uniform.
use std::fs;

#[derive(Clone, Copy)]
struct Sample { t: f64, nodes: f64, head: f64, total: f64 }

fn parse(path: &str) -> Vec<Sample> {
    let txt = match fs::read_to_string(path) { Ok(s) => s, Err(_) => return vec![] };
    let mut out = Vec::new();
    for line in txt.replace('\r', "\n").lines() {
        if !line.contains("queue") { continue; }
        let grab = |key: &str, sep: char| -> Option<f64> {
            let i = line.find(key)? + key.len();
            let rest = &line[i..];
            let end = rest.find(sep).unwrap_or(rest.len());
            rest[..end].trim().parse::<f64>().ok()
        };
        let nodes = grab("nodes~", ' ');
        let t = grab("t=", 's');
        let q = line.find("queue ").map(|i| &line[i + 6..]);
        if let (Some(nodes), Some(t), Some(q)) = (nodes, t, q) {
            let parts: Vec<&str> = q.split_whitespace().next().unwrap_or("").split('/').collect();
            if parts.len() == 2 {
                if let (Ok(h), Ok(tot)) = (parts[0].parse::<f64>(), parts[1].parse::<f64>()) {
                    out.push(Sample { t, nodes, head: h, total: tot });
                }
            }
        }
    }
    out
}

/// least-squares slope of y against t
fn slope(s: &[Sample], y: impl Fn(&Sample) -> f64) -> f64 {
    let n = s.len() as f64;
    if n < 2.0 { return 0.0; }
    let (mt, my) = (s.iter().map(|p| p.t).sum::<f64>() / n, s.iter().map(|p| y(p)).sum::<f64>() / n);
    let num: f64 = s.iter().map(|p| (p.t - mt) * (y(p) - my)).sum();
    let den: f64 = s.iter().map(|p| (p.t - mt).powi(2)).sum();
    if den == 0.0 { 0.0 } else { num / den }
}

fn human(secs: f64) -> String {
    if !secs.is_finite() || secs < 0.0 { return "not converging".into(); }
    if secs < 5400.0 { format!("{:.0} min", secs / 60.0) }
    else if secs < 172800.0 { format!("{:.1} h", secs / 3600.0) }
    else { format!("{:.1} days", secs / 86400.0) }
}

fn report(name: &str, path: &str) {
    let s = parse(path);
    if s.len() < 3 { println!("{:<6} not enough samples yet", name); return; }
    let t0 = s[0].t;
    let mut s = s.clone();
    for p in s.iter_mut() { p.t -= t0; }
    let s = &s[..];
    let last = *s.last().unwrap();
    if last.head >= last.total { println!("{:<6} finishing", name); return; }

    // recent window: last third of the samples, min 4
    let k = (s.len() / 3).max(4).min(s.len());
    let recent = &s[s.len() - k..];

    let dh = slope(recent, |p| p.head);          // tasks dispatched per second
    let dq = slope(recent, |p| p.total);         // tasks created per second
    let rate = slope(recent, |p| p.nodes);       // nodes per second

    // crossing of head(t) and total(t): gap closes at (total-head)/(dh-dq)
    let closing = dh - dq;
    let eta_recent = if closing > 0.0 { (last.total - last.head) / closing } else { f64::INFINITY };

    // whole-run average as a slower cross-check
    let dh_all = slope(&s, |p| p.head);
    let dq_all = slope(&s, |p| p.total);
    let eta_all = if dh_all - dq_all > 0.0 { (last.total - last.head) / (dh_all - dq_all) } else { f64::INFINITY };

    let pct = 100.0 * last.head / last.total;
    // Empirical distribution of node totals over every completed exhaustion in this project.
    // These searches are wildly non-uniform, so the honest ETA is a set of quantiles: "if this
    // one turns out to be a median-sized search, X; if it is a hard one, Y".
    // Every completed exhaustion in the project.  NOTE 134,631,158 = N=70's iso-alpha instance
    // (STATUS_TABLE L799): the largest ever, recorded in the ledger but not in the local logs, so a
    // log-derived histogram silently understates the tail by 3x.  It is the branch-matched
    // reference for any iso-alpha search.
    const HIST: [f64; 16] = [78.0, 489.0, 2107.0, 12440.0, 15493.0, 43992.0, 101807.0, 132519.0,
                             156646.0, 278197.0, 853731.0, 1222714.0, 1933605.0, 4334789.0,
                             43541916.0, 134631158.0];
    println!("{:<6} {:>5.1}% tasks ({:.0}/{:.0})   {:>6.0} nodes/s   {:>9.2}M nodes   running {}",
             name, pct, last.head, last.total, rate, last.nodes / 1e6, human(last.t));
    if rate > 0.0 {
        let q = |frac: f64| -> String {
            let i = ((HIST.len() - 1) as f64 * frac).round() as usize;
            let target = HIST[i];
            if target <= last.nodes { "already past".to_string() }
            else { human((target - last.nodes) / rate) }
        };
        println!("       if median-sized: {}   if 75th pct: {}   if 90th pct (43.5M): {}   if worst ever (134.6M): {}",
                 q(0.5), q(0.75), q(0.9), q(1.0));
    }
    if closing > 0.0 {
        println!("       task-crossing estimate: {}", human(eta_recent.min(eta_all)));
    } else {
        println!("       (work list still growing faster than consumed -- no task-based ETA yet)");
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    println!("{:<6} {:>5}  {:>18}  {:>12}  {:>9}  {}", "run", "prog", "tasks", "rate", "elapsed", "ETA range");
    for a in args.chunks(2) {
        if a.len() == 2 { report(&a[0], &a[1]); }
    }
}
