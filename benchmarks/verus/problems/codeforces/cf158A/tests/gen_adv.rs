use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_scores: &Vec<i32>,
    k: usize,
) -> (result: (Vec<i32>, usize))
    requires
        1 <= raw_scores.len() <= 50,
        1 <= k <= raw_scores.len(),
        forall|i: int| 0 <= i < raw_scores.len() ==> 0 <= #[trigger] raw_scores[i] <= 100,
        forall|i: int| 0 <= i < raw_scores.len() - 1 ==> #[trigger] raw_scores[i] >= raw_scores[i + 1],
    ensures
        1 <= result.0.len() <= 50,
        1 <= result.1 <= result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 100,
        forall|i: int| 0 <= i < result.0.len() - 1 ==> #[trigger] result.0[i] >= result.0[i + 1],
{
    let n = raw_scores.len();
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == raw_scores.len(),
            0 <= i <= n,
            out.len() == i,
            forall|j: int| 0 <= j < i as int ==> out[j] == raw_scores[j],
        decreases n - i,
    {
        out.push(raw_scores[i]);
        i = i + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < out.len() implies 0 <= #[trigger] out[j] <= 100 by {
            assert(out[j] == raw_scores[j]);
        }
        assert forall|j: int| 0 <= j < out.len() - 1 implies #[trigger] out[j] >= out[j + 1] by {
            assert(out[j] == raw_scores[j]);
            assert(out[j + 1] == raw_scores[j + 1]);
        }
    }
    (out, k)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng { state: u64 }
impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(1) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
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

fn build_input(n: usize, k: usize, scores: &[i32]) -> String {
    let mut s = format!("{} {}\n", n, k);
    let parts: Vec<String> = scores.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: usize) -> String { format!("{}\n", ans) }

fn make_test(rng: &mut Rng, mode: usize) -> (Vec<i32>, usize) {
    match mode {
        0 => (vec![rng.gen_range_i32(0, 100)], 1),
        1 => { let v = rng.gen_range_i32(0, 100); (vec![v; 50], 50) }
        2 => (vec![100; 50], 1),
        3 => (vec![0; 50], 50),
        4 => {
            let n = rng.gen_range_usize(1, 50);
            let k = rng.gen_range_usize(1, n);
            let mut v: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(0, 100)).collect();
            v.sort(); v.reverse();
            (v, k)
        }
        5 => {
            let n = 50;
            let k = rng.gen_range_usize(1, n);
            let mut v = Vec::with_capacity(n);
            for i in 0..n { v.push(100 - i as i32 * 2); }
            (v, k)
        }
        6 => {
            let n = rng.gen_range_usize(1, 50);
            let k = rng.gen_range_usize(1, n);
            (vec![50; n], k)
        }
        7 => {
            let n = rng.gen_range_usize(2, 50);
            let half = n / 2;
            let k = rng.gen_range_usize(1, n);
            let mut v: Vec<i32> = Vec::new();
            for _ in 0..half { v.push(50); }
            for _ in half..n { v.push(0); }
            (v, k)
        }
        8 => {
            let n = rng.gen_range_usize(1, 50);
            let k = n;
            let mut v: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(0, 100)).collect();
            v.sort(); v.reverse();
            (v, k)
        }
        9 => {
            let n = rng.gen_range_usize(1, 50);
            let k = 1;
            let mut v: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(0, 100)).collect();
            v.sort(); v.reverse();
            (v, k)
        }
        _ => {
            let n = rng.gen_range_usize(1, 50);
            let k = rng.gen_range_usize(1, n);
            let mut v: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(0, 100)).collect();
            v.sort(); v.reverse();
            (v, k)
        }
    }
}

fn main() {
    let mut rng = Rng::new(1);
    let modes = 10usize;
    let total = 200usize;

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;
    let mut idx = 0;
    while count < total {
        let mode = idx % modes;
        idx += 1;
        let (scores, k) = make_test(&mut rng, mode);
        let n = scores.len();
        if k < 1 || k > n { continue; }
        let inp = build_input(n, k, &scores);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::count_advancing(scores, k);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

