use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    c: i64,
    start: i64,
    gaps: &Vec<i64>,
) -> (result: (usize, i64, Vec<i64>))
    requires
        1 <= n <= 100_000,
        1 <= c <= 1_000_000_000,
        1 <= start <= 1_000_000_000,
        gaps.len() + 1 == n,
        forall|i: int| 0 <= i < gaps.len() ==> 1 <= #[trigger] gaps[i] <= 1000,
        start as int + 1000 * (n as int) <= 1_000_000_000,
    ensures
        ({
            let (rn, rc, rt) = result;
            &&& 1 <= rn <= 100_000
            &&& rn == rt.len()
            &&& 1 <= rc <= 1_000_000_000
            &&& rc == c
            &&& rn == n
            &&& (forall|u: int| 0 <= u < rn as int - 1 ==> #[trigger] rt[u] < rt[u + 1])
            &&& (forall|u: int| 0 <= u < rn as int ==> 1 <= #[trigger] rt[u] <= 1_000_000_000)
        }),
{
    let mut t: Vec<i64> = Vec::new();
    t.push(start);
    let mut cur: i64 = start;
    let mut i: usize = 0;

    while i < gaps.len()
        invariant
            0 <= i <= gaps.len(),
            t.len() == i + 1,
            gaps.len() + 1 == n,
            1 <= n <= 100_000,
            1 <= start <= 1_000_000_000,
            start as int + 1000 * (n as int) <= 1_000_000_000,
            cur as int == t[i as int] as int,
            cur as int >= start as int,
            cur as int <= start as int + 1000 * (i as int),
            t[0] == start,
            forall|k: int| 0 <= k < gaps.len() ==> 1 <= #[trigger] gaps[k] <= 1000,
            forall|k: int| 0 <= k < t.len() as int - 1 ==> #[trigger] t[k] < t[k + 1],
            forall|k: int| 0 <= k < t.len() ==> 1 <= #[trigger] t[k] <= 1_000_000_000,
        decreases gaps.len() - i,
    {
        let g = gaps[i];
        let new_cur: i64 = cur + g;
        assert(new_cur as int <= start as int + 1000 * (i as int) + 1000);
        assert(1000 * (i as int) + 1000 == 1000 * ((i as int) + 1));
        assert(new_cur as int <= 1_000_000_000);
        t.push(new_cur);
        cur = new_cur;
        i = i + 1;
    }

    assert(t.len() == n);
    (n, c, t)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

fn fmt_json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

struct Solution;
include!("../code.rs");

fn build_input(n: usize, c: i64, t: &[i64]) -> String {
    let mut s = format!("{} {}\n", n, c);
    let parts: Vec<String> = t.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: usize) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(71601);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |c: i64, t: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if t.is_empty() || t.len() > 100_000 { return; }
        if c < 1 || c > 1_000_000_000 { return; }
        for w in t.windows(2) { if w[0] >= w[1] { return; } }
        for &v in &t { if v < 1 || v > 1_000_000_000 { return; } }
        let key = format!("{}|{:?}", c, t);
        if !seen.insert(key) { return; }
        let inp = build_input(t.len(), c, &t);
        let ans = Solution::remaining_words(t.len(), c, t.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Boundaries
    emit(1, vec![1], &mut seen, &mut out, &mut count);
    emit(1_000_000_000, vec![1], &mut seen, &mut out, &mut count);
    // Single huge case
    let big: Vec<i64> = (1..=100_000i64).collect();
    emit(1, big.clone(), &mut seen, &mut out, &mut count);
    emit(2, big.clone(), &mut seen, &mut out, &mut count);
    emit(1_000_000_000, big.clone(), &mut seen, &mut out, &mut count);
    // Spaced out: gap > 1
    let big2: Vec<i64> = (0..100_000i64).map(|i| 2 * i + 1).collect();
    emit(1, big2.clone(), &mut seen, &mut out, &mut count);
    emit(2, big2.clone(), &mut seen, &mut out, &mut count);
    // Very wide gaps
    let wide: Vec<i64> = (0..10_000i64).map(|i| 1 + 100_000 * i).collect();
    emit(50_000, wide.clone(), &mut seen, &mut out, &mut count);
    emit(150_000, wide.clone(), &mut seen, &mut out, &mut count);

    while count < target {
        let n = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_usize(2, 100),
            2 => rng.gen_range_usize(100, 10_000),
            _ => rng.gen_range_usize(10_000, 100_000),
        };
        let c = rng.gen_range_i64(1, 1_000_000_000);
        // Build strictly-increasing sequence
        let mut t: Vec<i64> = Vec::with_capacity(n);
        let max_gap = 1_000_000_000i64 / (n as i64).max(1);
        let mut cur: i64 = 1;
        t.push(cur);
        for _ in 1..n {
            let g = rng.gen_range_i64(1, max_gap.max(1));
            cur = cur + g;
            if cur > 1_000_000_000 { break; }
            t.push(cur);
        }
        if t.len() != n { continue; }
        emit(c, t, &mut seen, &mut out, &mut count);
    }
}

