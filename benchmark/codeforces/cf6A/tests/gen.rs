use vstd::prelude::*;

verus! {

pub fn generate_test_case(s0: i32, s1: i32, s2: i32, s3: i32, mutation_kind: u8) -> (sticks: Vec<i32>)
    requires
        1 <= s0 as int <= 100,
        1 <= s1 as int <= 100,
        1 <= s2 as int <= 100,
        1 <= s3 as int <= 100,
    ensures
        sticks.len() == 4,
        forall|i: int| 0 <= i < 4 ==> 1 <= #[trigger] sticks[i] as int <= 100,
{
    let mut v: Vec<i32> = Vec::new();
    v.push(s0);
    v.push(s1);
    v.push(s2);
    v.push(s3);

    assert(v[0] == s0);
    assert(v[1] == s1);
    assert(v[2] == s2);
    assert(v[3] == s3);

    if mutation_kind == 1 && s0 < 100 {
        // nudge first element up
        v.set(0, s0 + 1);
        assert(v[0] == s0 + 1);
        assert(v[1] == s1);
        assert(v[2] == s2);
        assert(v[3] == s3);
    } else if mutation_kind == 2 && s0 > 1 {
        // nudge first element down
        v.set(0, s0 - 1);
        assert(v[0] == s0 - 1);
        assert(v[1] == s1);
        assert(v[2] == s2);
        assert(v[3] == s3);
    } else if mutation_kind == 3 {
        // set first element to 1 (min boundary)
        v.set(0, 1);
        assert(v[0] == 1);
        assert(v[1] == s1);
        assert(v[2] == s2);
        assert(v[3] == s3);
    } else if mutation_kind == 4 {
        // set first element to 100 (max boundary)
        v.set(0, 100);
        assert(v[0] == 100);
        assert(v[1] == s1);
        assert(v[2] == s2);
        assert(v[3] == s3);
    } else if mutation_kind == 5 {
        // set all elements equal to s0
        v.set(1, s0);
        v.set(2, s0);
        v.set(3, s0);
        assert(v[0] == s0);
        assert(v[1] == s0);
        assert(v[2] == s0);
        assert(v[3] == s0);
    } else if mutation_kind == 6 {
        // swap first two elements
        v.set(0, s1);
        v.set(1, s0);
        assert(v[0] == s1);
        assert(v[1] == s0);
        assert(v[2] == s2);
        assert(v[3] == s3);
    } else if mutation_kind == 7 {
        // set all to 1 (min boundary)
        v.set(0, 1);
        v.set(1, 1);
        v.set(2, 1);
        v.set(3, 1);
        assert(v[0] == 1);
        assert(v[1] == 1);
        assert(v[2] == 1);
        assert(v[3] == 1);
    } else if mutation_kind == 8 {
        // set all to 100 (max boundary)
        v.set(0, 100);
        v.set(1, 100);
        v.set(2, 100);
        v.set(3, 100);
        assert(v[0] == 100);
        assert(v[1] == 100);
        assert(v[2] == 100);
        assert(v[3] == 100);
    }
    // else: identity (mutation_kind == 0 or fallback)

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
// has_segment is defined in main.rs; replicate logic here.
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
    let target: usize = 100;
    let mut rng = Rng::new(6);
    let mut seen: HashSet<[i32; 4]> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
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

    // Examples
    emit([4, 2, 1, 3], &mut seen, &mut out, &mut count);
    emit([7, 2, 2, 4], &mut seen, &mut out, &mut count);
    emit([3, 5, 9, 1], &mut seen, &mut out, &mut count);

    // Edges
    emit([1, 1, 1, 1], &mut seen, &mut out, &mut count);
    emit([100, 100, 100, 100], &mut seen, &mut out, &mut count);
    emit([1, 1, 2, 2], &mut seen, &mut out, &mut count);
    emit([1, 2, 3, 5], &mut seen, &mut out, &mut count);
    emit([3, 4, 5, 99], &mut seen, &mut out, &mut count);
    emit([1, 1, 1, 100], &mut seen, &mut out, &mut count);
    emit([5, 5, 5, 1], &mut seen, &mut out, &mut count);

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

