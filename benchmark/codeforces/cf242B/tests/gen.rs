use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    lefts: Vec<i32>,
    widths: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        lefts.len() == widths.len(),
        1 <= lefts.len() <= 100_000,
        forall|i: int| 0 <= i < lefts.len() ==> 1 <= #[trigger] lefts[i],
        forall|i: int| 0 <= i < widths.len() ==> 0 <= #[trigger] widths[i],
        forall|i: int| 0 <= i < lefts.len()
            ==> (lefts[i] as int + widths[i] as int) <= 1_000_000_000,
        forall|i: int, j: int|
            0 <= i < j < lefts.len()
                ==> lefts[i] != lefts[j] || widths[i] != widths[j],
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= result.1[i] <= 1_000_000_000,
        forall|i: int, j: int|
            0 <= i < j < result.0.len() ==> result.0[i] != result.0[j] || result.1[i] != result.1[j],
{
    let n = lefts.len();

    // Build right[i] = lefts[i] + widths[i]
    let mut right: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n == lefts.len(),
            n == widths.len(),
            1 <= n <= 100_000,
            k <= n,
            right.len() == k,
            forall|j: int| 0 <= j < lefts.len() ==> 1 <= #[trigger] lefts[j],
            forall|j: int| 0 <= j < widths.len() ==> 0 <= #[trigger] widths[j],
            forall|j: int| 0 <= j < lefts.len()
                ==> (lefts[j] as int + widths[j] as int) <= 1_000_000_000,
            forall|j: int| 0 <= j < k as int ==> right[j] == (lefts[j] + widths[j]) as i32,
            forall|j: int| 0 <= j < k as int
                ==> 1 <= #[trigger] lefts[j] <= right[j] <= 1_000_000_000,
            forall|i2: int, j2: int|
                0 <= i2 < j2 < lefts.len()
                    ==> lefts[i2] != lefts[j2] || widths[i2] != widths[j2],
        decreases n - k,
    {
        let r_val = lefts[k] + widths[k];
        right.push(r_val);
        k += 1;
    }

    // Prove uniqueness of (lefts[i], right[i]) pairs
    proof {
        assert forall|i2: int, j2: int|
            0 <= i2 < j2 < n as int
        implies
            lefts@[i2] != lefts@[j2] || right@[i2] != right@[j2]
        by {
            if lefts@[i2] == lefts@[j2] {
                // widths differ, so rights differ
                assert(widths@[i2] != widths@[j2]);
                assert(right@[i2] == lefts@[i2] + widths@[i2]);
                assert(right@[j2] == lefts@[j2] + widths@[j2]);
            }
        }
    }

    (lefts, right)
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

fn build_input(left: &[i32], right: &[i32]) -> String {
    let n = left.len();
    let mut s = format!("{}\n", n);
    for i in 0..n {
        s.push_str(&format!("{} {}\n", left[i], right[i]));
    }
    s
}

fn build_output(ans: i32) -> String {
    if ans == 0 { "-1\n".to_string() } else { format!("{}\n", ans) }
}

fn random_unique_segments(rng: &mut Rng, n: usize, max: i64) -> (Vec<i32>, Vec<i32>) {
    let mut seen = HashSet::new();
    let mut left = Vec::with_capacity(n);
    let mut right = Vec::with_capacity(n);
    let mut tries = 0;
    while left.len() < n && tries < n * 100 {
        tries += 1;
        let l = rng.gen_range_i64(1, max) as i32;
        let r = rng.gen_range_i64(l as i64, max) as i32;
        if seen.insert((l, r)) {
            left.push(l);
            right.push(r);
        }
    }
    (left, right)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(242);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 2, 3], vec![1, 2, 3]),
        (vec![1, 2, 1, 7, 7, 10], vec![5, 3, 10, 10, 7, 10]),
    ];
    for (l, r) in &examples {
        if count >= target { break; }
        let inp = build_input(l, r);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::find_covering_segment(l.clone(), r.clone());
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 6 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(3, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 200),
            4 => rng.gen_range_usize(200, 1000),
            _ => rng.gen_range_usize(1000, 10000),
        };
        let max_val = match tries % 3 {
            0 => 100,
            1 => 1_000_000,
            _ => 1_000_000_000i64,
        };
        let (l, r) = random_unique_segments(&mut rng, n, max_val);
        if l.is_empty() { continue; }
        let inp = build_input(&l, &r);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::find_covering_segment(l, r);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

