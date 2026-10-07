use vstd::prelude::*;

verus! {

pub open spec fn count_val(v: int, x: int, a: int, b: int, c: int) -> int {
    (if x == v { 1int } else { 0 })
    + (if a == v { 1int } else { 0 })
    + (if b == v { 1int } else { 0 })
    + (if c == v { 1int } else { 0 })
}

// perm: 4 distinct values from {0,1,2,3} where 1,2,3 each appear exactly once
// and 0 appears exactly once. Positions: 0=x, 1=a, 2=b, 3=c
// We parameterize by which position gets the 0 (zero_pos in 0..4),
// and the permutation of (1,2,3) for the other three positions.
pub fn generate_test_case(
    zero_pos: u8,  // 0..=3
    perm: u8,      // 0..=5 -- which permutation of (1,2,3)
) -> (result: (i32, i32, i32, i32))
    requires
        zero_pos <= 3,
        perm <= 5,
    ensures ({
        let (x, a, b, c) = result;
        &&& 1 <= x <= 3
        &&& 0 <= a <= 3
        &&& 0 <= b <= 3
        &&& 0 <= c <= 3
        &&& count_val(1, x as int, a as int, b as int, c as int) == 1
        &&& count_val(2, x as int, a as int, b as int, c as int) == 1
        &&& count_val(3, x as int, a as int, b as int, c as int) == 1
    }),
{
    // Get the three non-zero values in order based on perm
    let (v1, v2, v3): (i32, i32, i32) = match perm {
        0 => (1, 2, 3),
        1 => (1, 3, 2),
        2 => (2, 1, 3),
        3 => (2, 3, 1),
        4 => (3, 1, 2),
        _ => (3, 2, 1),
    };

    // zero_pos can't be 0 because x must be >= 1
    // If caller passes zero_pos == 0, remap to 1
    let zp: u8 = if zero_pos == 0 { 1 } else { zero_pos };

    let (x, a, b, c): (i32, i32, i32, i32) = if zp == 1 {
        (v1, 0, v2, v3)
    } else if zp == 2 {
        (v1, v2, 0, v3)
    } else {
        // zp == 3
        (v1, v2, v3, 0)
    };

    (x, a, b, c)
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

type TC = (i32, i32, i32, i32);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (x, a, b, c) in cases {
        s.push_str(&format!("{}\n{} {} {}\n", x, a, b, c));
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (x, a, b, c) in cases {
        let ans = Solution::can_open_all_doors(*a, *b, *c, *x);
        s.push_str(if ans { "YES\n" } else { "NO\n" });
    }
    s
}

fn enumerate_all() -> Vec<TC> {
    let mut out = Vec::new();
    for x in 1..=3 {
        let others: Vec<i32> = (1..=3i32).filter(|&v| v != x).collect();
        for zero_pos in 0..3 {
            let remaining: Vec<usize> = (0..3).filter(|&i| i != zero_pos).collect();
            for perm in 0..2 {
                let mut slots = [0i32; 3];
                slots[zero_pos] = 0;
                if perm == 0 {
                    slots[remaining[0]] = others[0];
                    slots[remaining[1]] = others[1];
                } else {
                    slots[remaining[0]] = others[1];
                    slots[remaining[1]] = others[0];
                }
                out.push((x, slots[0], slots[1], slots[2]));
            }
        }
    }
    out
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1709);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    let all_cases = enumerate_all();

    while count < target && tries < 100000 {
        tries += 1;
        // Most are full size t=18, some are small
        let t: usize = match rng.gen_range_usize(0, 4) {
            0 => 18,
            1 => 1,
            2 => 2,
            3 => rng.gen_range_usize(5, 18),
            _ => rng.gen_range_usize(1, 18),
        };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let idx = rng.gen_range_usize(0, all_cases.len() - 1);
            cases.push(all_cases[idx]);
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

