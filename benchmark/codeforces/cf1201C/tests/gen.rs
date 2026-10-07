use vstd::prelude::*;

verus! {

/// Sum of the first `end` elements of `deltas` as mathematical ints.
pub open spec fn sum_deltas(deltas: Seq<i64>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

/// sum_deltas is monotonically non-decreasing when all deltas >= 0.
proof fn lemma_sum_deltas_mono(deltas: Seq<i64>, a: int, b: int)
    requires
        0 <= a <= b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 0i64,
    ensures
        sum_deltas(deltas, a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if a < b {
        lemma_sum_deltas_mono(deltas, a, b - 1);
    }
}

/// sum_deltas is non-negative when all deltas >= 0.
proof fn lemma_sum_deltas_nonneg(deltas: Seq<i64>, end: int)
    requires
        0 <= end <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 0i64,
    ensures
        sum_deltas(deltas, end) >= 0,
    decreases end,
{
    if end > 0 {
        lemma_sum_deltas_nonneg(deltas, end - 1);
    }
}

pub open spec fn spec_sorted(a: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}

pub fn generate_test_case(
    deltas: &Vec<i64>,
    base: i64,
    k: i64,
    mutation_kind: u8,
) -> (result: (usize, i64, Vec<i64>))
    requires
        deltas.len() % 2 == 0,
        0 <= deltas.len(),
        deltas.len() + 1 <= 200000,
        1 <= base,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1000000000,
        1 <= k <= 1000000000,
    ensures
        1 <= result.0 <= 200000,
        result.0 % 2 == 1,
        result.2.len() == result.0,
        1 <= result.1 <= 1000000000,
        forall|i: int| 0 <= i < result.0 ==> 1 <= #[trigger] result.2[i] <= 1000000000,
        spec_sorted(result.2@),
{
    proof {
        lemma_sum_deltas_nonneg(deltas@, deltas.len() as int);
    }

    let n: usize = deltas.len() + 1;
    let actual_k: i64 = if mutation_kind == 1 {
        1i64
    } else if mutation_kind == 2 {
        1000000000i64
    } else {
        k
    };

    if mutation_kind == 3 {
        // Flat array: all elements equal to base
        let mut a: Vec<i64> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                0 <= idx <= n,
                a.len() == idx,
                n == deltas.len() + 1,
                n <= 200000,
                1 <= base <= 1000000000,
                forall|j: int| 0 <= j < a.len() ==> #[trigger] a[j] == base,
            decreases n - idx,
        {
            a.push(base);
            idx = idx + 1;
        }
        assert forall|i2: int, j2: int| 0 <= i2 <= j2 < a.len() implies a[i2] <= a[j2] by {}
        (n, k, a)
    } else {
        // Build sorted array from cumulative sums of deltas
        let mut a: Vec<i64> = Vec::new();
        a.push(base);

        let mut idx: usize = 0;
        while idx < deltas.len()
            invariant
                0 <= idx <= deltas.len(),
                a.len() == idx + 1,
                n == deltas.len() + 1,
                n <= 200000,
                1 <= base,
                forall|j: int| 0 <= j < deltas.len() ==> 0 <= #[trigger] deltas[j],
                base as int + sum_deltas(deltas@, deltas.len() as int) <= 1000000000,
                forall|j: int| 0 <= j <= idx as int ==>
                    (#[trigger] a[j]) as int == base as int + sum_deltas(deltas@, j),
                forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1000000000,
                forall|j: int, l: int| 0 <= j < l < a.len() ==> a[j] <= a[l],
            decreases deltas.len() - idx,
        {
            let prev = a[idx];
            let new_val: i64 = {
                proof {
                    lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
                }
                prev + deltas[idx]
            };

            a.push(new_val);

            assert forall|j: int, l: int| 0 <= j < l < a.len() implies a[j] <= a[l] by {
                if l < a.len() - 1 {
                } else {
                }
            }

            idx = idx + 1;
        }

        (n, actual_k, a)
    }
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
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
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

    // Examples
    emit(2, vec![1,3,5], &mut seen, &mut out, &mut count);
    emit(5, vec![1,2,1,1,1], &mut seen, &mut out, &mut count);
    emit(7, vec![1,2,3,4,5,6,7], &mut seen, &mut out, &mut count);

    // Edge cases
    emit(1, vec![1], &mut seen, &mut out, &mut count);
    emit(1_000_000_000, vec![1], &mut seen, &mut out, &mut count);
    emit(1, vec![1_000_000_000], &mut seen, &mut out, &mut count);
    emit(1, vec![1,1,1], &mut seen, &mut out, &mut count);
    emit(1_000_000_000, vec![1,1,1], &mut seen, &mut out, &mut count);
    emit(1, vec![1_000_000_000,1_000_000_000,1_000_000_000], &mut seen, &mut out, &mut count);

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let mut n = match tries % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(5, 30),
            3 => rng.gen_range_usize(20, 100),
            _ => rng.gen_range_usize(50, 500),
        };
        if n % 2 == 0 { n += 1; }
        let max_val = match tries % 4 {
            0 => 10i64,
            1 => 100,
            2 => 10_000,
            _ => 1_000_000_000,
        };
        let k = rng.gen_range_i64(1, 1_000_000_000);
        let v = random_array(&mut rng, n, max_val);
        emit(k, v, &mut seen, &mut out, &mut count);
    }
}

