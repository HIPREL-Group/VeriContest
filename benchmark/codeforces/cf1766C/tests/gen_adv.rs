use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    pattern: &Vec<u8>,  // each element is 0, 1, or 2: 0 means only row0 is B, 1 means only row1 is B, 2 means both are B
) -> (result: (usize, Vec<i64>, Vec<i64>))
    requires
        m >= 1,
        m <= 200_000,
        pattern.len() == m,
        forall|i: int| 0 <= i < pattern.len() ==> (#[trigger] pattern[i]) <= 2,
    ensures
        result.0 == m,
        result.1.len() == m,
        result.2.len() == m,
        forall|k: int| 0 <= k < m as int ==> (#[trigger] result.1[k] == 0 || result.1[k] == 1),
        forall|k: int| 0 <= k < m as int ==> (#[trigger] result.2[k] == 0 || result.2[k] == 1),
        forall|k: int| 0 <= k < m as int ==> (#[trigger] result.1[k] == 1 || result.2[k] == 1),
{
    let mut row0: Vec<i64> = Vec::new();
    let mut row1: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < m
        invariant
            0 <= i <= m,
            row0.len() == i,
            row1.len() == i,
            pattern.len() == m,
            forall|k: int| 0 <= k < pattern.len() ==> (#[trigger] pattern[k]) <= 2,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] row0[k] == 0 || row0[k] == 1),
            forall|k: int| 0 <= k < i as int ==> (#[trigger] row1[k] == 0 || row1[k] == 1),
            forall|k: int| 0 <= k < i as int ==> (#[trigger] row0[k] == 1 || row1[k] == 1),
        decreases m - i,
    {
        let p = pattern[i];
        if p == 0 {
            row0.push(1);
            row1.push(0);
        } else if p == 1 {
            row0.push(0);
            row1.push(1);
        } else {
            row0.push(1);
            row1.push(1);
        }
        i = i + 1;
    }

    (m, row0, row1)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed.wrapping_add(1)) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
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

type TC = (usize, String, String);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (m, r0, r1) in cases {
        s.push_str(&format!("{}\n{}\n{}\n", m, r0, r1));
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (m, r0, r1) in cases {
        let row0: Vec<i64> = r0.as_bytes().iter().map(|&b| if b == b'B' { 1 } else { 0 }).collect();
        let row1: Vec<i64> = r1.as_bytes().iter().map(|&b| if b == b'B' { 1 } else { 0 }).collect();
        let ans = Solution::can_paint_wall(*m, row0, row1);
        s.push_str(if ans { "YES\n" } else { "NO\n" });
    }
    s
}

fn random_valid(rng: &mut Rng, m: usize) -> (String, String) {
    let mut r0 = String::with_capacity(m);
    let mut r1 = String::with_capacity(m);
    for _ in 0..m {
        let mode = rng.gen_range_usize(0, 2);
        match mode {
            0 => { r0.push('B'); r1.push('W'); }
            1 => { r0.push('W'); r1.push('B'); }
            _ => { r0.push('B'); r1.push('B'); }
        }
    }
    (r0, r1)
}

fn gen_case(rng: &mut Rng, mode: usize) -> TC {
    match mode {
        0 => {
            let m = 1;
            let r0 = if rng.next_u64() % 2 == 0 { "B" } else { "W" };
            let r1 = if r0 == "W" { "B" } else { if rng.next_u64() % 2 == 0 { "B" } else { "W" } };
            (m, r0.to_string(), r1.to_string())
        }
        1 => {
            // both rows all B
            let m = rng.gen_range_usize(1, 100);
            (m, "B".repeat(m), "B".repeat(m))
        }
        2 => {
            // top all B, bottom all W
            let m = rng.gen_range_usize(1, 100);
            (m, "B".repeat(m), "W".repeat(m))
        }
        3 => {
            // alternating
            let m = rng.gen_range_usize(2, 100);
            let r0: String = (0..m).map(|i| if i % 2 == 0 { 'B' } else { 'W' }).collect();
            let r1: String = (0..m).map(|i| if i % 2 == 0 { 'W' } else { 'B' }).collect();
            (m, r0, r1)
        }
        4 => {
            // moderate-large
            let m = rng.gen_range_usize(500, 2000);
            let (r0, r1) = random_valid(rng, m);
            (m, r0, r1)
        }
        _ => {
            let m = rng.gen_range_usize(1, 200);
            let (r0, r1) = random_valid(rng, m);
            (m, r0, r1)
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1766);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 100000 {
        tries += 1;
        let t: usize = if count % 5 == 0 { rng.gen_range_usize(2, 20) } else { 1 };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let mode = (rng.next_u64() as usize) % 6;
            cases.push(gen_case(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

