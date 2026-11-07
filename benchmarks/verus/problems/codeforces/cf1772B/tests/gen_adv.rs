use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: i32, b: i32, c: i32, d: i32) -> (res: (i32, i32, i32, i32))
    requires
        1 <= a <= 100,
        1 <= b <= 100,
        1 <= c <= 100,
        1 <= d <= 100,
        a != b,
        a != c,
        a != d,
        b != c,
        b != d,
        c != d,
    ensures
        ({
            let (ra, rb, rc, rd) = res;
            &&& 1 <= ra <= 100
            &&& 1 <= rb <= 100
            &&& 1 <= rc <= 100
            &&& 1 <= rd <= 100
            &&& ra != rb
            &&& ra != rc
            &&& ra != rd
            &&& rb != rc
            &&& rb != rd
            &&& rc != rd
        }),
{
    (a, b, c, d)
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
    let mut chosen: Vec<i32> = Vec::with_capacity(4);
    while chosen.len() < 4 {
        let v = rng.gen_range_i32(1, 100);
        if !chosen.contains(&v) { chosen.push(v); }
    }
    (chosen[0], chosen[1], chosen[2], chosen[3])
}

fn gen_case(rng: &mut Rng, mode: usize) -> TC {
    match mode {
        0 => {
            // sorted: 1 2; 3 4
            let v = rng.gen_range_i32(1, 25);
            (v, v + 1, v + 2, v + 3)
        }
        1 => {
            // 90 deg rotated: 3 1; 4 2
            let v = rng.gen_range_i32(1, 25);
            (v + 2, v, v + 3, v + 1)
        }
        2 => {
            // permutation that's NOT achievable, e.g. (1, 4, 2, 3)
            let mut chosen: Vec<i32> = Vec::with_capacity(4);
            while chosen.len() < 4 {
                let v = rng.gen_range_i32(1, 100);
                if !chosen.contains(&v) { chosen.push(v); }
            }
            chosen.sort();
            // (smallest, largest, middle1, middle2) which often is NO
            (chosen[0], chosen[3], chosen[1], chosen[2])
        }
        _ => random_distinct_4(rng)
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1772);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 100000 {
        tries += 1;
        let t: usize = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_usize(2, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(2, 50),
        };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let mode = (rng.next_u64() as usize) % 4;
            cases.push(gen_case(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

