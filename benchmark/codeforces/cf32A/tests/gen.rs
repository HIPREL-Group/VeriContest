use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_heights: Vec<i64>,
    d: i64,
    mutation_kind: u8,
) -> (result: (usize, i64, Vec<i64>))
    requires
        1 <= raw_heights.len() <= 1000,
        1 <= d <= 1000000000,
        forall|i: int| 0 <= i < raw_heights.len() ==> 0 <= #[trigger] raw_heights[i] as int <= 1000000000,
    ensures
        1 <= result.0 <= 1000,
        result.2.len() == result.0,
        1 <= result.1 <= 1000000000,
        forall|i: int| 0 <= i < result.2.len() ==> 0 <= #[trigger] result.2[i] as int <= 1000000000,
{
    let n = raw_heights.len();
    if mutation_kind == 0 {
        (n, d, raw_heights)
    } else if mutation_kind == 1 {
        // all heights equal
        let mut h = raw_heights;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == n,
                1 <= n <= 1000,
                forall|j: int| 0 <= j < i ==> h[j] == 100i64,
                forall|j: int| i <= j < h.len() ==> 0 <= #[trigger] h[j] as int <= 1000000000,
            decreases h.len() - i,
        {
            h.set(i, 100i64);
            i += 1;
        }
        (n, d, h)
    } else if mutation_kind == 2 {
        // d very large
        (n, 1000000000, raw_heights)
    } else if mutation_kind == 3 {
        // d very small
        (n, 1, raw_heights)
    } else {
        (n, d, raw_heights)
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
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

fn build_input(n: usize, d: i64, heights: &[i64]) -> String {
    let parts: Vec<String> = heights.iter().map(|x| x.to_string()).collect();
    format!("{} {}\n{}\n", n, d, parts.join(" "))
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(32);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |n: usize, d: i64, heights: &Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if n < 1 || n > 1000 || heights.len() != n { return; }
        if d < 1 || d > 1000000000 { return; }
        let inp = build_input(n, d, heights);
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::count_recon_pairs(n, d, heights.clone());
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Examples
    emit(5, 10, &vec![10, 20, 50, 60, 65], &mut seen, &mut out, &mut count);
    emit(5, 1, &vec![55, 30, 29, 31, 55], &mut seen, &mut out, &mut count);

    // Small cases
    emit(1, 1, &vec![5], &mut seen, &mut out, &mut count);
    emit(2, 1, &vec![1, 2], &mut seen, &mut out, &mut count);
    emit(2, 1000000000, &vec![1, 1000000000], &mut seen, &mut out, &mut count);

    while count < target {
        let n = rng.gen_range_usize(1, 100);
        let d = rng.gen_range_i64(1, 1000);
        let heights: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(0, 1000)).collect();
        emit(n, d, &heights, &mut seen, &mut out, &mut count);
    }
}
