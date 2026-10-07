use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: i32, b: i32, c: i32, d: i32) -> (sticks: Vec<i32>)
    requires
        1 <= a <= 100,
        1 <= b <= 100,
        1 <= c <= 100,
        1 <= d <= 100,
    ensures
        sticks.len() == 4,
        forall|i: int| 0 <= i < 4 ==> 1 <= #[trigger] sticks[i] as int <= 100,
{
    let mut v: Vec<i32> = Vec::new();
    v.push(a);
    v.push(b);
    v.push(c);
    v.push(d);
    assert(v.len() == 4);
    assert(v[0] == a);
    assert(v[1] == b);
    assert(v[2] == c);
    assert(v[3] == d);
    v
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        lo + (self.next_u64() as i32).rem_euclid(hi - lo + 1)
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
impl Solution {
    pub fn has_segment(sticks: Vec<i32>) -> bool {
        let n = sticks.len();
        for i in 0..n {
            for j in 0..n {
                for k in 0..n {
                    if i != j && i != k && j != k {
                        let a = sticks[i] as i64;
                        let b = sticks[j] as i64;
                        let c = sticks[k] as i64;
                        if a + b == c || a + c == b || b + c == a {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }
}

fn build_input(s: &[i32; 4]) -> String { format!("{} {} {} {}\n", s[0], s[1], s[2], s[3]) }

fn classify(sticks: &[i32; 4]) -> &'static str {
    let v: Vec<i32> = sticks.iter().copied().collect();
    if Solution::has_triangle(v.clone()) { "TRIANGLE" }
    else if Solution::has_segment(v) { "SEGMENT" }
    else { "IMPOSSIBLE" }
}

fn build_output(label: &str) -> String { format!("{}\n", label) }

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(601);
    let mut seen: HashSet<[i32; 4]> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |sticks: [i32; 4], seen: &mut HashSet<[i32; 4]>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        for &v in &sticks { if v < 1 || v > 100 { return; } }
        if !seen.insert(sticks) { return; }
        let inp = build_input(&sticks);
        let label = classify(&sticks);
        let outs = build_output(label);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // All same value
    for v in 1..=100i32 { emit([v, v, v, v], &mut seen, &mut out, &mut count); }

    // (a, a, a, b) varieties
    for a in [1, 2, 5, 10, 50, 99, 100i32] {
        for b in 1..=100i32 {
            emit([a, a, a, b], &mut seen, &mut out, &mut count);
            if count >= target { break; }
        }
    }

    // a+b=c situations (degenerate)
    for a in 1..=20i32 {
        for b in a..=20i32 {
            let c = a + b;
            if c <= 100 {
                emit([a, b, c, 1], &mut seen, &mut out, &mut count);
                emit([a, b, c, 100], &mut seen, &mut out, &mut count);
            }
        }
    }

    while count < target {
        let s = [
            rng.gen_range_i32(1, 100),
            rng.gen_range_i32(1, 100),
            rng.gen_range_i32(1, 100),
            rng.gen_range_i32(1, 100),
        ];
        emit(s, &mut seen, &mut out, &mut count);
    }
}

