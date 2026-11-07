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

pub fn generate_test_case(seed_ax: i64, seed_ay: i64, seed_bx: i64, seed_by: i64, seed_cx: i64, seed_cy: i64, mutation_kind: u8) -> (result: (i64, i64, i64, i64, i64, i64))
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
    if mutation_kind % 2 == 0 {
        distinct_points(seed_ax, seed_ay, seed_bx, seed_by, seed_cx, seed_cy)
    } else {
        distinct_points(seed_ax, seed_ay, seed_cx, seed_cy, seed_bx, seed_by)
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

fn random_case(rng: &mut Rng, max: i64) -> Case {
    (
        rng.gen_range_i64(-max, max),
        rng.gen_range_i64(-max, max),
        rng.gen_range_i64(-max, max),
        rng.gen_range_i64(-max, max),
        rng.gen_range_i64(-max, max),
        rng.gen_range_i64(-max, max),
    )
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1845);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Example
    let example: Vec<Case> = vec![
        (0, 0, 1, 1, 2, 2),
        (0, 0, 1, 1, -1, -1),
        (0, 0, 2, 0, 5, 0),
        (1, 3, 2, 2, 3, 1),
    ];
    {
        let example: Vec<Case> = example.into_iter()
            .map(|c| generate_test_case(c.0, c.1, c.2, c.3, c.4, c.5, 0)).collect();
        let inp = build_input(&example);
        let answers: Vec<i64> = example.iter().map(|&c| solve(c)).collect();
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Single edges
    let edges: Vec<Case> = vec![
        (0, 0, 0, 0, 0, 0),
        (1_000_000_000, 1_000_000_000, -1_000_000_000, -1_000_000_000, 1_000_000_000, 1_000_000_000),
        (0, 0, 100, 100, 50, 50),
        (0, 0, -100, 0, 100, 0),  // opposite x
        (0, 0, 0, 100, 0, -100), // opposite y
    ];
    for &ec in &edges {
        if count >= target { break; }
        let cases = vec![generate_test_case(ec.0, ec.1, ec.2, ec.3, ec.4, ec.5, 0)];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|&c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    // Bundled multi-test
    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(2, 8) } else { rng.gen_range_usize(5, 30) };
        let mut cases: Vec<Case> = Vec::new();
        for _ in 0..t {
            let max = match rng.next_u64() % 3 {
                0 => 10,
                1 => 1000,
                _ => 1_000_000_000,
            };
            let c = random_case(&mut rng, max);
            cases.push(generate_test_case(c.0, c.1, c.2, c.3, c.4, c.5, 0));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|&c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}
