use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_d: Vec<u32>,
    a: usize,
    b: usize,
    mutation_kind: u8,
) -> (result: (usize, Vec<u32>, usize, usize))
    requires
        2 <= raw_d.len() + 1 <= 100,
        forall|i: int| 0 <= i < raw_d.len() ==> 1 <= #[trigger] raw_d[i] as int <= 100,
        1 <= a < b <= raw_d.len() + 1,
    ensures
        2 <= result.0 <= 100,
        result.1.len() == result.0 - 1,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] as int <= 100,
        1 <= result.2 < result.3 <= result.0,
{
    let n = raw_d.len() + 1;
    if mutation_kind == 0 {
        (n, raw_d, a, b)
    } else if mutation_kind == 1 {
        // set all to 1
        let mut d = raw_d;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n - 1,
                2 <= n <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 1u32,
                forall|j: int| i <= j < d.len() ==> 1 <= #[trigger] d[j] as int <= 100,
            decreases d.len() - i,
        {
            d.set(i, 1u32);
            i += 1;
        }
        (n, d, a, b)
    } else if mutation_kind == 2 {
        // set all to 100
        let mut d = raw_d;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n - 1,
                2 <= n <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 100u32,
                forall|j: int| i <= j < d.len() ==> 1 <= #[trigger] d[j] as int <= 100,
            decreases d.len() - i,
        {
            d.set(i, 100u32);
            i += 1;
        }
        (n, d, a, b)
    } else if mutation_kind == 3 {
        // a = 1, b = n
        (n, raw_d, 1, n)
    } else if mutation_kind == 4 && a < b - 1 {
        // shrink range
        (n, raw_d, a, b - 1)
    } else if mutation_kind == 5 {
        (n, raw_d, 1, 2)
    } else {
        (n, raw_d, a, b)
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
    fn gen_range_u32(&mut self, lo: u32, hi: u32) -> u32 {
        lo + (self.next_u64() as u32) % (hi - lo + 1)
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

fn build_input(n: usize, d: &[u32], a: usize, b: usize) -> String {
    let parts: Vec<String> = d.iter().map(|x| x.to_string()).collect();
    format!("{}\n{}\n{} {}\n", n, parts.join(" "), a, b)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(38);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |n: usize, d: &Vec<u32>, a: usize, b: usize, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if n < 2 || n > 100 { return; }
        if d.len() != n - 1 { return; }
        if a < 1 || b > n || a >= b { return; }
        let inp = build_input(n, d, a, b);
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::years_needed(n, d.clone(), a, b);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Examples from problem
    emit(3, &vec![5, 6], 1, 2, &mut seen, &mut out, &mut count);
    emit(3, &vec![5, 6], 1, 3, &mut seen, &mut out, &mut count);

    // Boundary
    emit(2, &vec![1], 1, 2, &mut seen, &mut out, &mut count);
    emit(2, &vec![100], 1, 2, &mut seen, &mut out, &mut count);
    emit(100, &vec![100; 99], 1, 100, &mut seen, &mut out, &mut count);

    // Random testcases
    while count < target {
        let n = rng.gen_range_usize(2, 100);
        let d: Vec<u32> = (0..n-1).map(|_| rng.gen_range_u32(1, 100)).collect();
        let a = rng.gen_range_usize(1, n - 1);
        let b = rng.gen_range_usize(a + 1, n);
        emit(n, &d, a, b, &mut seen, &mut out, &mut count);
    }
}
