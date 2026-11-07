use vstd::prelude::*;

verus! {

pub fn generate_test_case(heights: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= heights.len() <= 100000,
        forall|i: int| 0 <= i < heights.len() ==> 1 <= #[trigger] heights[i] <= 10000,
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 10000,
{
    if mutation_kind == 0 {
        // identity
        heights
    } else if mutation_kind == 1 {
        // set last element to 1 (boundary low)
        let mut h = heights;
        let last = h.len() - 1;
        h.set(last, 1);
        h
    } else if mutation_kind == 2 {
        // set last element to 10000 (boundary high)
        let mut h = heights;
        let last = h.len() - 1;
        h.set(last, 10000);
        h
    } else if mutation_kind == 3 {
        // set first element to 1
        let mut h = heights;
        h.set(0, 1);
        h
    } else if mutation_kind == 4 {
        // set first element to 10000
        let mut h = heights;
        h.set(0, 10000);
        h
    } else if mutation_kind == 5 && heights.len() < 100000 {
        // grow by one element (push 1)
        let mut h = heights;
        h.push(1);
        h
    } else if mutation_kind == 6 && heights.len() > 1 {
        // shrink by one element (pop)
        let mut h = heights;
        h.pop();
        h
    } else if mutation_kind == 7 {
        // nudge last element up (if < 10000)
        let mut h = heights;
        let last = h.len() - 1;
        if h[last] < 10000 {
            h.set(last, h[last] + 1);
        }
        h
    } else if mutation_kind == 8 {
        // nudge last element down (if > 1)
        let mut h = heights;
        let last = h.len() - 1;
        if h[last] > 1 {
            h.set(last, h[last] - 1);
        }
        h
    } else if mutation_kind == 9 {
        // set all elements to 1
        let mut h = heights;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == heights.len(),
                1 <= h.len() <= 100000,
                forall|j: int| 0 <= j < i as int ==> h[j] == 1i32,
                forall|j: int| i as int <= j < h.len() as int ==> h[j] == heights[j],
            decreases h.len() - i,
        {
            h.set(i, 1);
            i += 1;
        }
        h
    } else if mutation_kind == 10 {
        // set all elements to 10000
        let mut h = heights;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == heights.len(),
                1 <= h.len() <= 100000,
                forall|j: int| 0 <= j < i as int ==> h[j] == 10000i32,
                forall|j: int| i as int <= j < h.len() as int ==> h[j] == heights[j],
            decreases h.len() - i,
        {
            h.set(i, 10000);
            i += 1;
        }
        h
    } else {
        // fallback: identity
        heights
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

fn build_input(heights: &[i32]) -> String {
    let mut s = format!("{}\n", heights.len());
    for h in heights {
        s.push_str(&format!("{}\n", h));
    }
    s
}

fn build_output(ans: i64) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(265);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2],
        vec![2, 1, 2, 1, 1],
        vec![1],
        vec![10000],
    ];
    for ex in &examples {
        if count >= target { break; }
        let inp = build_input(ex);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::min_time(ex.clone());
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 6 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 200),
            4 => rng.gen_range_usize(200, 1000),
            _ => rng.gen_range_usize(1000, 10000),
        };
        let max_h = match tries % 3 {
            0 => 10i64,
            1 => 100i64,
            _ => 10000i64,
        };
        let heights: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(1, max_h) as i32).collect();
        let inp = build_input(&heights);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::min_time(heights);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

