use vstd::prelude::*;

verus! {

pub fn coordinate(value: i64) -> (result: i64)
    ensures 1 <= result <= 100000000,
{
    if value < 1 { 1 } else if value > 100000000 { 100000000 } else { value }
}

pub fn distinct_points(
    ax: i64, ay: i64, bx: i64, by: i64, cx: i64, cy: i64,
) -> (result: (i64, i64, i64, i64, i64, i64))
    ensures
        1 <= result.0 <= 100000000,
        1 <= result.1 <= 100000000,
        1 <= result.2 <= 100000000,
        1 <= result.3 <= 100000000,
        1 <= result.4 <= 100000000,
        1 <= result.5 <= 100000000,
        !(result.0 == result.2 && result.1 == result.3),
        !(result.0 == result.4 && result.1 == result.5),
        !(result.2 == result.4 && result.3 == result.5),
{
    let ax = coordinate(ax);
    let ay = coordinate(ay);
    let mut bx = coordinate(bx);
    let by = coordinate(by);
    let cx = coordinate(cx);
    let mut cy = coordinate(cy);
    if ax == bx && ay == by {
        bx = if ax < 100000000 { ax + 1 } else { 1 };
    }
    if (cx == ax && cy == ay) || (cx == bx && cy == by) {
        // At most two y coordinates are forbidden for this x coordinate.
        cy = if (cx != ax || ay != 1) && (cx != bx || by != 1) { 1 }
             else if (cx != ax || ay != 2) && (cx != bx || by != 2) { 2 }
             else { 3 };
    }
    (ax, ay, bx, by, cx, cy)
}

pub fn generate_test_case(ax: i64, ay: i64, bx: i64, by: i64, cx: i64, cy: i64) -> (result: (i64, i64, i64, i64, i64, i64))
    ensures
        1 <= result.0 <= 100000000,
        1 <= result.1 <= 100000000,
        1 <= result.2 <= 100000000,
        1 <= result.3 <= 100000000,
        1 <= result.4 <= 100000000,
        1 <= result.5 <= 100000000,
        !(result.0 == result.2 && result.1 == result.3),
        !(result.0 == result.4 && result.1 == result.5),
        !(result.2 == result.4 && result.3 == result.5),
{
    distinct_points(ax, ay, bx, by, cx, cy)
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

type Case = (i64, i64, i64, i64, i64, i64);

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(ax, ay, bx, by, cx, cy) in cases {
        s.push_str(&format!("{} {} {} {} {} {}\n", ax, ay, bx, by, cx, cy));
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn solve(c: Case) -> i64 {
    Solution::min_meeting_cells(c.0, c.1, c.2, c.3, c.4, c.5)
}

fn pick_adv(rng: &mut Rng) -> Case {
    match rng.next_u64() % 6 {
        0 => {
            // All extreme positive
            let a = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
            (a, a, 1_000_000_000, 1_000_000_000, 1_000_000_000, 1_000_000_000)
        }
        1 => {
            // B and C on same side x
            let ax = rng.gen_range_i64(-1_000_000_000, 0);
            let ay = rng.gen_range_i64(-1_000_000_000, 0);
            (ax, ay, ax + rng.gen_range_i64(1, 1_000_000_000), ay, ax + rng.gen_range_i64(1, 1_000_000_000), ay)
        }
        2 => {
            // B and C exactly at A
            let a = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
            (a, a, a, a, a, a)
        }
        3 => {
            // Opposite sides
            let ax = 0; let ay = 0;
            let b = rng.gen_range_i64(1, 1_000_000_000);
            (ax, ay, b, 0, -b, 0)
        }
        4 => {
            // Random within full range
            (
                rng.gen_range_i64(-1_000_000_000, 1_000_000_000),
                rng.gen_range_i64(-1_000_000_000, 1_000_000_000),
                rng.gen_range_i64(-1_000_000_000, 1_000_000_000),
                rng.gen_range_i64(-1_000_000_000, 1_000_000_000),
                rng.gen_range_i64(-1_000_000_000, 1_000_000_000),
                rng.gen_range_i64(-1_000_000_000, 1_000_000_000),
            )
        }
        _ => {
            // Small values
            (
                rng.gen_range_i64(-100, 100),
                rng.gen_range_i64(-100, 100),
                rng.gen_range_i64(-100, 100),
                rng.gen_range_i64(-100, 100),
                rng.gen_range_i64(-100, 100),
                rng.gen_range_i64(-100, 100),
            )
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(10, 30) } else { rng.gen_range_usize(20, 100) };
        let mut cases: Vec<Case> = Vec::new();
        for _ in 0..t {
            let c = pick_adv(&mut rng);
            cases.push(generate_test_case(c.0, c.1, c.2, c.3, c.4, c.5));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|&c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}
