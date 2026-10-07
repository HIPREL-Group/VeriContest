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

pub fn generate_test_case(
    deltas: &Vec<i64>,
    base: i64,
    k: i64,
    mutation_kind: u8,
) -> (result: (Vec<i64>, i64))
    requires
        deltas.len() < 200_000,
        1 <= base <= 1_000_000_000,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
        base as int - sum_deltas(deltas@, deltas.len() as int) >= 1,
        0 <= k <= 1_000_000_000_000_000,
    ensures
        1 <= result.0.len() <= 200_000,
        0 <= result.1 <= 1_000_000_000_000_000,
        forall |j: int| 0 <= j < result.0.len() ==> 1 <= #[trigger] result.0[j] <= 1_000_000_000,
        forall |x: int, y: int| 0 <= x <= y < result.0.len() ==> result.0[x] >= result.0[y],
{
    proof {
        lemma_sum_deltas_nonneg(deltas@, deltas.len() as int);
    }

    let actual_k: i64 = if mutation_kind == 1 {
        0i64
    } else if mutation_kind == 2 {
        1_000_000_000_000_000i64
    } else {
        k
    };

    if mutation_kind == 3 {
        // Flat array: all elements equal to base
        let n: usize = deltas.len() + 1;
        let mut a: Vec<i64> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                0 <= idx <= n,
                a.len() == idx,
                n == deltas.len() + 1,
                n <= 200_000,
                1 <= base <= 1_000_000_000,
                forall|j: int| 0 <= j < a.len() ==> #[trigger] a[j] == base,
            decreases n - idx,
        {
            a.push(base);
            idx = idx + 1;
        }
        assert forall|x2: int, y2: int| 0 <= x2 <= y2 < a.len() implies a[x2] >= a[y2] by {}
        (a, actual_k)
    } else {
        // Build non-increasing array: a[0] = base, a[i+1] = a[i] - deltas[i]
        let mut a: Vec<i64> = Vec::new();
        a.push(base);

        let mut idx: usize = 0;
        while idx < deltas.len()
            invariant
                0 <= idx <= deltas.len(),
                a.len() == idx + 1,
                deltas.len() < 200_000,
                1 <= base <= 1_000_000_000,
                forall|j: int| 0 <= j < deltas.len() ==> 0 <= #[trigger] deltas[j],
                base as int - sum_deltas(deltas@, deltas.len() as int) >= 1,
                forall|j: int| 0 <= j <= idx as int ==>
                    (#[trigger] a[j]) as int == base as int - sum_deltas(deltas@, j),
                forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
                forall|j: int, l: int| 0 <= j < l < a.len() ==> a[j] >= a[l],
            decreases deltas.len() - idx,
        {
            let prev = a[idx];
            let new_val: i64 = {
                proof {
                    // prev == base - sum_deltas(deltas@, idx)
                    // new_val == prev - deltas[idx] == base - sum_deltas(deltas@, idx+1)
                    // sum_deltas(deltas@, idx+1) <= sum_deltas(deltas@, len)
                    // so new_val >= base - sum_deltas(deltas@, len) >= 1
                    lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
                    // Also new_val <= prev <= base <= 1_000_000_000
                    // And sum_deltas(deltas@, idx+1) >= 0, so new_val <= base
                    lemma_sum_deltas_nonneg(deltas@, (idx + 1) as int);
                }
                prev - deltas[idx]
            };

            a.push(new_val);

            // Prove non-increasing: new element <= all previous elements
            assert forall|j: int, l: int| 0 <= j < l < a.len() implies a[j] >= a[l] by {
                if l < a.len() - 1 {
                    // Both old elements — covered by loop invariant
                } else {
                    // l == a.len() - 1, the new element
                    // a[l] == new_val <= prev == a[idx]
                    // For j <= idx: a[j] >= a[idx] >= new_val == a[l]
                }
            }

            idx = idx + 1;
        }

        (a, actual_k)
    }
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
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

fn solve(mut a: Vec<i64>, k: i64) -> u64 {
    a.sort_unstable_by(|x, y| y.cmp(x));
    Solution::optimal_score(a, k)
}

fn build_input(cases: &[(Vec<i64>, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, k) in cases {
        s.push_str(&format!("{} {}\n", a.len(), k));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[u64]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    let example: Vec<(Vec<i64>, i64)> = vec![
        (vec![1, 10], 5),
        (vec![3, 1, 2, 4], 6),
        (vec![6, 9], 4),
        (vec![15, 12, 10], 0),
    ];
    {
        let answers: Vec<u64> = example.iter().map(|(a, k)| solve(a.clone(), *k)).collect();
        let inp = build_input(&example);
        let outp = build_output(&answers);
        let key = format!("{:?}", example);
        if seen.insert(key) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    while count < target {
        let t: usize = if count < 10 { 1 }
                       else if count < 30 { rng.gen_range_usize(2, 5) }
                       else if count < 60 { rng.gen_range_usize(3, 10) }
                       else { rng.gen_range_usize(5, 20) };

        let mut cases: Vec<(Vec<i64>, i64)> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(2, 30);
            let k = rng.gen_range_i64(0, 100);
            let max_a = if count < 30 { 20 } else { 1000 };
            let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, max_a)).collect();
            cases.push((a, k));
        }
        let key = format!("{:?}", cases);
        if !seen.insert(key) { continue; }
        let answers: Vec<u64> = cases.iter().map(|(a, k)| solve(a.clone(), *k)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

