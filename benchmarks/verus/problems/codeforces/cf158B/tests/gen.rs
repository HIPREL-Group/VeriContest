use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    s1: i32,
    s2: i32,
    s3: i32,
    s4: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, i32, i32))
    requires
        0 <= s1,
        0 <= s2,
        0 <= s3,
        0 <= s4,
        (s1 + s2 + s3 + s4) <= 100_000i32,
    ensures
        result.0 >= 0,
        result.1 >= 0,
        result.2 >= 0,
        result.3 >= 0,
        (result.0 + result.1 + result.2 + result.3) <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        (s1, s2, s3, s4)
    } else if mutation_kind == 1 {
        // zero out c1
        (0, s2, s3, s4)
    } else if mutation_kind == 2 {
        // zero out c2
        (s1, 0, s3, s4)
    } else if mutation_kind == 3 {
        // zero out c3
        (s1, s2, 0, s4)
    } else if mutation_kind == 4 {
        // zero out c4
        (s1, s2, s3, 0)
    } else if mutation_kind == 5 {
        // all zeros
        (0, 0, 0, 0)
    } else if mutation_kind == 6 {
        // concentrate all in c1
        let total = s1 + s2 + s3 + s4;
        (total, 0, 0, 0)
    } else if mutation_kind == 7 {
        // concentrate all in c4
        let total = s1 + s2 + s3 + s4;
        (0, 0, 0, total)
    } else if mutation_kind == 8 {
        // swap c1 and c2
        (s2, s1, s3, s4)
    } else if mutation_kind == 9 {
        // swap c3 and c4
        (s1, s2, s4, s3)
    } else if mutation_kind == 10 && s2 > 0 {
        // nudge: c1 up by 1, c2 down by 1
        (s1 + 1, s2 - 1, s3, s4)
    } else if mutation_kind == 11 && s4 > 0 {
        // nudge: c3 up by 1, c4 down by 1
        (s1, s2, s3 + 1, s4 - 1)
    } else if mutation_kind == 12 {
        // halve all
        (s1 / 2, s2 / 2, s3 / 2, s4 / 2)
    } else {
        // fallback: identity
        (s1, s2, s3, s4)
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
        // High 32 bits XOR'd with low 32 bits for better mixing
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as u128;
        (lo as i128 + (v % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as usize;
        lo + v % (hi - lo + 1)
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

fn build_input(groups: &[i32]) -> String {
    let mut s = format!("{}\n", groups.len());
    let parts: Vec<String> = groups.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i32) -> String { format!("{}\n", ans) }

fn compute(groups: &[i32]) -> i32 {
    let mut c1 = 0i32; let mut c2 = 0i32; let mut c3 = 0i32; let mut c4 = 0i32;
    for &g in groups {
        if g == 1 { c1 += 1; }
        else if g == 2 { c2 += 1; }
        else if g == 3 { c3 += 1; }
        else { c4 += 1; }
    }
    Solution::min_taxis(c1, c2, c3, c4)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen: HashSet<String> = HashSet::new();

    let mut emit = |groups: Vec<i32>, count: &mut usize, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>| {
        if *count >= target { return; }
        let inp = build_input(&groups);
        if !seen.insert(inp.clone()) { return; }
        let ans = compute(&groups);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    emit(vec![1, 2, 4, 3, 3], &mut count, &mut seen, &mut out);
    emit(vec![2, 3, 4, 4, 2, 1, 3, 1], &mut count, &mut seen, &mut out);
    emit(vec![1], &mut count, &mut seen, &mut out);
    emit(vec![2], &mut count, &mut seen, &mut out);
    emit(vec![3], &mut count, &mut seen, &mut out);
    emit(vec![4], &mut count, &mut seen, &mut out);
    emit(vec![1; 4], &mut count, &mut seen, &mut out);
    emit(vec![1; 5], &mut count, &mut seen, &mut out);
    emit(vec![2; 4], &mut count, &mut seen, &mut out);
    emit(vec![3, 1], &mut count, &mut seen, &mut out);
    emit(vec![3, 1, 1], &mut count, &mut seen, &mut out);
    emit(vec![3, 3], &mut count, &mut seen, &mut out);
    emit(vec![2, 2, 1], &mut count, &mut seen, &mut out);
    emit(vec![2, 2, 1, 1], &mut count, &mut seen, &mut out);

    while count < target {
        let n = rng.gen_range_usize(1, 100);
        let groups: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(1, 4) as i32).collect();
        emit(groups, &mut count, &mut seen, &mut out);
    }
}

