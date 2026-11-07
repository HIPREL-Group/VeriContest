use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k: i64,
    base: i64,
    steps: &Vec<i64>,
) -> (result: (usize, i64, Vec<i64>))
    requires
        1 <= n <= 200000,
        n % 2 == 1,
        steps.len() == n,
        1 <= k <= 1000000000,
        1 <= base <= 1000000000,
        forall|i: int| 0 <= i < steps.len() ==> 0 <= #[trigger] steps[i] <= 1000000000 - base,
    ensures
        result.0 == n,
        result.1 == k,
        result.2.len() == n,
        1 <= result.0 <= 200000,
        result.0 % 2 == 1,
        1 <= result.1 <= 1000000000,
        forall|i: int| 0 <= i < result.2.len() ==> 1 <= #[trigger] result.2[i] <= 1000000000,
        forall|i: int, j: int| 0 <= i <= j < result.2.len() ==> result.2[i] <= result.2[j],
{
    // Build array a[i] = base + cumulative_sum(steps[0..=i])
    // This gives a non-decreasing array with values in [base, 1_000_000_000].
    let mut a: Vec<i64> = Vec::new();
    let mut cum: i64 = 0;
    let mut i: usize = 0;

    while i < n
        invariant
            i <= n,
            a.len() == i,
            steps.len() == n,
            1 <= base <= 1000000000,
            0 <= cum <= 1000000000 - base,
            forall|j: int| 0 <= j < steps.len() ==> 0 <= #[trigger] steps[j] <= 1000000000 - base,
            forall|j: int| 0 <= j < i as int ==> base <= #[trigger] a[j] <= 1000000000,
            forall|j1: int, j2: int| 0 <= j1 <= j2 < i as int ==> a[j1] <= a[j2],
            forall|j: int| 0 <= j < i as int ==> #[trigger] a[j] >= base + cum - (if j + 1 == i as int { steps[j] as int } else { 0int }) ==> true,
            i as int > 0 ==> a[i as int - 1] as int == base as int + cum as int,
        decreases n - i,
    {
        let s = steps[i];
        // cum + s <= 1000000000 - base? We need to maintain invariant.
        // steps[i] <= 1000000000 - base, and cum <= 1000000000 - base.
        // Sum could exceed. We must clamp.
        let new_cum: i64 = if cum + s > 1000000000 - base { 1000000000 - base } else { cum + s };
        assert(0 <= new_cum <= 1000000000 - base);
        assert(new_cum >= cum);
        let val: i64 = base + new_cum;
        assert(base <= val <= 1000000000);
        
        let prev_last: i64 = if i > 0 { a[i - 1] } else { base };
        
        proof {
            if i > 0 {
                assert(a[i as int - 1] as int == base as int + cum as int);
                assert(val as int == base as int + new_cum as int);
                assert(new_cum >= cum);
                assert(val >= a[i as int - 1]);
            }
        }
        
        a.push(val);
        
        proof {
            assert(a.len() == i + 1);
            assert(a[i as int] == val);
            assert forall|j1: int, j2: int| 0 <= j1 <= j2 < (i + 1) as int implies a[j1] <= a[j2] by {
                if j2 < i as int {
                    // covered by previous invariant
                } else {
                    // j2 == i
                    assert(a[j2] == val);
                    if j1 < i as int {
                        if i > 0 {
                            assert(a[i as int - 1] <= val);
                            assert(a[j1] <= a[i as int - 1]);
                        }
                    }
                }
            }
        }
        
        cum = new_cum;
        i = i + 1;
    }

    (n, k, a)
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

fn build_input(k: i64, a: &[i64]) -> String {
    let mut s = format!("{} {}\n", a.len(), k);
    let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i64) -> String { format!("{}\n", ans) }

fn solve(k: i64, a_unsorted: &[i64]) -> i64 {
    let mut a = a_unsorted.to_vec();
    a.sort();
    Solution::max_median(a.len(), k, a)
}

fn random_array(rng: &mut Rng, len: usize, max_val: i64) -> Vec<i64> {
    (0..len).map(|_| rng.gen_range_i64(1, max_val)).collect()
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(987654321);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |k: i64, a: Vec<i64>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a.is_empty() || a.len() % 2 == 0 { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= a.len() as u64; h = h.wrapping_mul(1099511628211);
        h ^= k as u64; h = h.wrapping_mul(1099511628211);
        for &x in &a { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        if !seen.insert(h) { return; }
        let inp = build_input(k, &a);
        let ans = solve(k, &a);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Pattern variations
    for &n in &[1usize, 3, 5, 9, 99, 999, 9999, 99_999] {
        emit(1, vec![1i64; n], &mut seen, &mut out, &mut count);
        emit(1_000_000_000, vec![1i64; n], &mut seen, &mut out, &mut count);
        emit(1_000_000_000, vec![1_000_000_000i64; n], &mut seen, &mut out, &mut count);
        let v: Vec<i64> = (0..n).map(|i| (i as i64) + 1).collect();
        emit(1_000_000_000, v, &mut seen, &mut out, &mut count);
    }

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let mut n = match tries % 6 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(5, 50),
            2 => rng.gen_range_usize(50, 500),
            3 => rng.gen_range_usize(500, 5_000),
            4 => rng.gen_range_usize(5_000, 30_000),
            _ => rng.gen_range_usize(30_000, 100_000),
        };
        if n % 2 == 0 { n += 1; }
        let max_val = match tries % 4 {
            0 => 10i64,
            1 => 1_000,
            2 => 1_000_000,
            _ => 1_000_000_000,
        };
        let k = match tries % 3 {
            0 => 1i64,
            1 => rng.gen_range_i64(1, 1_000_000),
            _ => rng.gen_range_i64(1, 1_000_000_000),
        };
        let v = random_array(&mut rng, n, max_val);
        emit(k, v, &mut seen, &mut out, &mut count);
    }
}

