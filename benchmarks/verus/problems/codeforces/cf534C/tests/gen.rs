use vstd::prelude::*;

verus! {

pub open spec fn sum_maxima(maxima: Seq<i64>, end: int) -> int
    recommends 0 <= end <= maxima.len(),
    decreases end,
{
    if end <= 0 {
        0
    } else {
        sum_maxima(maxima, end - 1) + maxima[end - 1] as int
    }
}

proof fn sum_maxima_all_ones(seq: Seq<i64>, n: int)
    requires
        0 <= n <= seq.len(),
        forall|k: int| 0 <= k < n ==> seq[k] == 1i64,
    ensures
        sum_maxima(seq, n) == n,
    decreases n,
{
    if n > 0 {
        assert(seq[n - 1] == 1i64);
        sum_maxima_all_ones(seq, n - 1);
    }
}

pub fn generate_test_case(
    n: usize,
    vals: Vec<i64>,
    total_raw: i64,
    mutation_kind: u8,
) -> (result: (i64, Vec<i64>))
    requires
        1 <= n <= 200_000,
        vals.len() == n,
        forall|i: int| 0 <= i < n as int ==> 1 <= #[trigger] vals[i] <= 1_000_000,
    ensures
        1 <= result.1.len() <= 200_000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 1_000_000,
        result.1.len() as int <= result.0 as int <= sum_maxima(result.1@, result.1.len() as int),
{
    // Compute sum_all and prove it equals sum_maxima
    let mut sum_all: i64 = 0;
    let mut idx: usize = 0;
    while idx < n
        invariant
            0 <= idx <= n,
            vals.len() == n,
            1 <= n <= 200_000,
            forall|j: int| 0 <= j < n as int ==> 1 <= #[trigger] vals[j] <= 1_000_000,
            sum_all as int == sum_maxima(vals@, idx as int),
            idx as int <= sum_all as int,
            sum_all as int <= idx as int * 1_000_000,
        decreases n - idx,
    {
        sum_all = sum_all + vals[idx];
        idx = idx + 1;
    }
    // Now: sum_all == sum_maxima(vals@, n), n <= sum_all <= n * 1_000_000

    if mutation_kind == 0 {
        // clamp total_raw to [n, sum_all]
        let total = if total_raw < n as i64 {
            n as i64
        } else if total_raw > sum_all {
            sum_all
        } else {
            total_raw
        };
        (total, vals)
    } else if mutation_kind == 1 {
        // min total = n
        (n as i64, vals)
    } else if mutation_kind == 2 {
        // max total = sum_all
        (sum_all, vals)
    } else if mutation_kind == 3 {
        // midpoint total
        let diff = sum_all - n as i64;
        let half = diff / 2;
        let total = n as i64 + half;
        (total, vals)
    } else if mutation_kind == 4 && sum_all > n as i64 {
        // near min
        (n as i64 + 1, vals)
    } else if mutation_kind == 5 && sum_all > n as i64 {
        // near max
        (sum_all - 1, vals)
    } else if mutation_kind == 6 {
        // all dice = 1, total = n
        let mut y = vals;
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                y.len() == n,
                1 <= n <= 200_000,
                forall|k: int| 0 <= k < j as int ==> #[trigger] y[k] == 1,
                forall|k: int| j as int <= k < n as int ==> 1 <= #[trigger] y[k] <= 1_000_000,
            decreases n - j,
        {
            y.set(j, 1i64);
            j = j + 1;
        }
        assert forall|k: int| 0 <= k < y.len() implies 1 <= #[trigger] y[k] <= 1_000_000 by {}
        proof {
            sum_maxima_all_ones(y@, n as int);
        }
        (n as i64, y)
    } else {
        // fallback: min total
        (n as i64, vals)
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
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
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

fn build_input(total: i64, maxima: &[i64]) -> String {
    let n = maxima.len();
    let mut s = format!("{} {}\n", n, total);
    let parts: Vec<String> = maxima.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: &[i64]) -> String {
    let parts: Vec<String> = ans.iter().map(|x| x.to_string()).collect();
    format!("{}\n", parts.join(" "))
}

fn main() {
    let target_count: usize = 100;
    let mut rng = Rng::new(534);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |total: i64, maxima: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let n = maxima.len();
        if n < 1 { return; }
        let sum: i64 = maxima.iter().sum();
        if total < n as i64 || total > sum { return; }
        for &d in &maxima { if d < 1 || d > 1_000_000 { return; } }
        let key = format!("{}_{:?}", total, maxima);
        if !seen.insert(key) { return; }
        let result = Solution::impossible_face_counts(total, maxima.clone());
        let inp = build_input(total, &maxima);
        let outp = build_output(&result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    emit(8, vec![4, 4], &mut seen, &mut out, &mut count);
    emit(3, vec![5], &mut seen, &mut out, &mut count);
    emit(3, vec![2, 3], &mut seen, &mut out, &mut count);

    // Edge
    emit(1, vec![1], &mut seen, &mut out, &mut count);
    emit(1, vec![1_000_000], &mut seen, &mut out, &mut count);
    emit(1_000_000, vec![1_000_000], &mut seen, &mut out, &mut count);
    emit(2, vec![1, 1], &mut seen, &mut out, &mut count);
    emit(10, vec![5, 5], &mut seen, &mut out, &mut count);
    emit(2, vec![1; 2], &mut seen, &mut out, &mut count);

    while count < target_count {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 30),
            2 => rng.gen_range_usize(30, 200),
            3 => rng.gen_range_usize(200, 2000),
            _ => rng.gen_range_usize(1000, 10_000),
        };
        let maxima: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1_000_000) as i64).collect();
        let sum: i64 = maxima.iter().sum();
        let total = rng.gen_range_i64(n as i64, sum);
        emit(total, maxima, &mut seen, &mut out, &mut count);
    }
}

