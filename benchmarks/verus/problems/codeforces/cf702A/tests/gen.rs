use vstd::prelude::*;

verus! {

/// Constructs a valid `(n, a)` pair for max_increasing_subarray_len,
/// applying mutation_kind to diversify the generated inputs.
///
/// Mutations:
///   0 — identity (copy seed elements as-is)
///   1 — set all elements to 1 (min boundary)
///   2 — set all elements to 1_000_000_000 (max boundary)
///   3 — nudge first element up: if < 1_000_000_000, increment by 1
///   4 — nudge first element down: if > 1, decrement by 1
///   5 — set last element to 1 (min boundary element)
///   6 — set last element to 1_000_000_000 (max boundary element)
///   7 — swap first and last elements
pub fn generate_test_case(
    elems: &Vec<i64>,
    mutation_kind: u8,
) -> (result: (usize, Vec<i64>))
    requires
        1 <= elems.len() <= 100_000,
        forall|t: int| 0 <= t < elems.len() ==> 1 <= #[trigger] elems[t] <= 1_000_000_000,
    ensures
        1 <= result.0 <= 100_000,
        result.0 == result.1.len(),
        forall|t: int| 0 <= t < result.1.len() ==> 1 <= #[trigger] result.1[t] <= 1_000_000_000,
{
    let n = elems.len();

    if mutation_kind == 1 {
        // set all elements to 1
        let mut out: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == k,
                forall|j: int| 0 <= j < k ==> #[trigger] out[j] == 1i64,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - k,
        {
            out.push(1);
            k = k + 1;
        }
        (n, out)
    } else if mutation_kind == 2 {
        // set all elements to 1_000_000_000
        let mut out: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == k,
                forall|j: int| 0 <= j < k ==> #[trigger] out[j] == 1_000_000_000i64,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - k,
        {
            out.push(1_000_000_000);
            k = k + 1;
        }
        (n, out)
    } else if mutation_kind == 3 {
        // nudge first element up
        let mut out: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == k,
                forall|i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 1_000_000_000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - k,
        {
            if k == 0 && elems[0] < 1_000_000_000 {
                out.push(elems[0] + 1);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        (n, out)
    } else if mutation_kind == 4 {
        // nudge first element down
        let mut out: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == k,
                forall|i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 1_000_000_000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - k,
        {
            if k == 0 && elems[0] > 1 {
                out.push(elems[0] - 1);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        (n, out)
    } else if mutation_kind == 5 {
        // set last element to 1
        let mut out: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == k,
                forall|i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 1_000_000_000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - k,
        {
            if k == n - 1 {
                out.push(1);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        (n, out)
    } else if mutation_kind == 6 {
        // set last element to 1_000_000_000
        let mut out: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == k,
                forall|i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 1_000_000_000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - k,
        {
            if k == n - 1 {
                out.push(1_000_000_000);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        (n, out)
    } else if mutation_kind == 7 && n >= 2 {
        // swap first and last elements
        let mut out: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                2 <= n <= 100_000,
                out.len() == k,
                forall|i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 1_000_000_000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - k,
        {
            if k == 0 {
                out.push(elems[n - 1]);
            } else if k == n - 1 {
                out.push(elems[0]);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        (n, out)
    } else {
        // identity (mutation_kind == 0 or fallback)
        let mut out: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == k,
                forall|i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 1_000_000_000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - k,
        {
            out.push(elems[k]);
            k = k + 1;
        }
        (n, out)
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

fn build_input(a: &[i64]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: usize) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(702);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a.is_empty() || a.len() > 100_000 { return; }
        for &v in &a { if v < 1 || v > 1_000_000_000 { return; } }
        let key = format!("{:?}", a);
        if !seen.insert(key) { return; }
        let inp = build_input(&a);
        let ans = Solution::max_increasing_subarray_len(a.len(), a.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(vec![1, 7, 2, 11, 15], &mut seen, &mut out, &mut count);
    emit(vec![100, 100, 100, 100, 100, 100], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 3], &mut seen, &mut out, &mut count);

    // Edges
    emit(vec![1], &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![1, 1, 1, 1], &mut seen, &mut out, &mut count);
    emit((1..=10i64).collect(), &mut seen, &mut out, &mut count);
    emit({ let mut v: Vec<i64> = (1..=10).collect(); v.reverse(); v }, &mut seen, &mut out, &mut count);

    while count < target {
        let n = rng.gen_range_usize(1, 200);
        let max_v: i64 = match rng.gen_range_usize(0, 4) {
            0 => 2,
            1 => 5,
            2 => 100,
            _ => 1_000_000_000,
        };
        let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, max_v)).collect();
        emit(a, &mut seen, &mut out, &mut count);
    }
}

