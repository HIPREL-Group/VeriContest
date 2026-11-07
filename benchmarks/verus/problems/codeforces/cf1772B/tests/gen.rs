use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    v1: i32,
    v2: i32,
    v3: i32,
    v4: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, i32, i32))
    requires
        1 <= v1 && v1 <= 97,
        v1 < v2 && v2 <= 98,
        v2 < v3 && v3 <= 99,
        v3 < v4 && v4 <= 100,
    ensures
        1 <= result.0 && result.0 <= 100,
        1 <= result.1 && result.1 <= 100,
        1 <= result.2 && result.2 <= 100,
        1 <= result.3 && result.3 <= 100,
        result.0 != result.1,
        result.0 != result.2,
        result.0 != result.3,
        result.1 != result.2,
        result.1 != result.3,
        result.2 != result.3,
{
    if mutation_kind == 0 {
        (v1, v2, v3, v4)           // natural order
    } else if mutation_kind == 1 {
        (v4, v3, v2, v1)           // reverse
    } else if mutation_kind == 2 {
        (v1, v3, v2, v4)           // swap middle pair
    } else if mutation_kind == 3 {
        (v2, v1, v4, v3)           // swap within pairs
    } else if mutation_kind == 4 {
        (v3, v4, v1, v2)           // swap halves
    } else if mutation_kind == 5 {
        (v1, v4, v2, v3)           // spread
    } else if mutation_kind == 6 {
        (v2, v3, v1, v4)           // rotate first three
    } else if mutation_kind == 7 {
        (v4, v1, v3, v2)           // misc permutation
    } else if mutation_kind == 8 {
        (v3, v1, v4, v2)           // misc permutation
    } else if mutation_kind == 9 {
        (v2, v4, v1, v3)           // misc permutation
    } else {
        (v1, v2, v3, v4)           // fallback
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % r) as i64) as i32
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

type TC = (i32, i32, i32, i32);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, b, c, d) in cases {
        s.push_str(&format!("{} {}\n{} {}\n", a, b, c, d));
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (a, b, c, d) in cases {
        let ans = Solution::can_make_beautiful(*a, *b, *c, *d);
        s.push_str(if ans { "YES\n" } else { "NO\n" });
    }
    s
}

fn random_distinct_4(rng: &mut Rng) -> TC {
    // pick 4 distinct values from 1..=100
    let mut chosen: Vec<i32> = Vec::with_capacity(4);
    while chosen.len() < 4 {
        let v = rng.gen_range_i32(1, 100);
        if !chosen.contains(&v) { chosen.push(v); }
    }
    (chosen[0], chosen[1], chosen[2], chosen[3])
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1772);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<TC> = vec![
        (1, 3, 2, 4),
        (1, 2, 3, 4),
        (4, 3, 2, 1),
        (2, 1, 4, 3),
        (3, 1, 2, 4),
        (5, 8, 6, 12),
        (10, 20, 30, 40),
        (100, 99, 98, 97),
    ];

    for ex in &examples {
        if count >= target { break; }
        let cases = vec![ex.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { rng.gen_range_usize(1, 5) } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            cases.push(random_distinct_4(&mut rng));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

