use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: i64,
    l: i64,
    t: i64,
    p_choice: i64,
) -> (res: (i64, i64, i64, i64))
    requires
        1 <= n <= 100_000_000,
        1 <= l <= 1_000_000_000,
        1 <= t <= 1_000_000_000,
        1 <= p_choice <= 10_000_000_000_000_000,
    ensures
        ({
            let (rn, rp, rl, rt) = res;
            &&& 1 <= rn <= 100_000_000
            &&& 1 <= rp <= 10_000_000_000_000_000
            &&& 1 <= rl <= 1_000_000_000
            &&& 1 <= rt <= 1_000_000_000
            &&& ((rn + 6) / 7 / 2) * (rl + 2 * rt) <= 9_000_000_000_000_000_000
            &&& rp <= rn * rl + ((rn + 6) / 7) * rt
        }),
{
    // Compute maximum possible p
    let tasks: i64 = (n + 6) / 7;
    // n <= 1e8, tasks <= ~1.5e7
    // n * l <= 1e8 * 1e9 = 1e17
    // tasks * t <= 1.5e7 * 1e9 = 1.5e16
    // Total <= ~1.15e17, fits in i64.
    assert(tasks <= n);
    assert(n as int * l as int <= 100_000_000 * 1_000_000_000) by (nonlinear_arith)
        requires n <= 100_000_000, l <= 1_000_000_000, n >= 1, l >= 1;
    assert(tasks as int * t as int <= 100_000_000 * 1_000_000_000) by (nonlinear_arith)
        requires tasks <= n, n <= 100_000_000, t <= 1_000_000_000, tasks >= 0, t >= 1;

    let max_p: i64 = n * l + tasks * t;

    assert(max_p >= 1) by (nonlinear_arith)
        requires n >= 1, l >= 1, tasks >= 0, t >= 1, max_p == n * l + tasks * t;

    // Clamp p_choice to [1, min(max_p, 10^16)]
    let cap: i64 = if max_p < 10_000_000_000_000_000 { max_p } else { 10_000_000_000_000_000 };
    assert(cap >= 1);

    let p: i64 = if p_choice <= cap { p_choice } else { cap };

    assert(p >= 1);
    assert(p <= cap);
    assert(p <= max_p);

    // Now check the nonlinear constraint: ((n+6)/7/2) * (l + 2*t) <= 9e18
    // (n+6)/7/2 <= tasks/2 <= tasks <= ~1.5e7
    // l + 2*t <= 3e9
    // product <= 4.5e16, well under 9e18
    let pairs: i64 = tasks / 2;
    let pair_pts: i64 = l + 2 * t;
    assert(pairs <= tasks);
    assert(pair_pts <= 3_000_000_000);
    assert(pairs as int * pair_pts as int <= 100_000_000 * 3_000_000_000) by (nonlinear_arith)
        requires pairs <= 100_000_000, pair_pts <= 3_000_000_000, pairs >= 0, pair_pts >= 0;

    (n, p, l, t)
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

type Case = (i64, i64, i64, i64);

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(n, p, l, t) in cases {
        s.push_str(&format!("{} {} {} {}\n", n, p, l, t));
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn solve(c: Case) -> i64 {
    Solution::max_rest_days(c.0, c.1, c.2, c.3)
}

fn pick_adv(rng: &mut Rng) -> Case {
    match rng.next_u64() % 6 {
        0 => {
            // Max n, max p
            (100_000_000, 10_000_000_000_000_000, 1_000_000_000, 1_000_000_000)
        }
        1 => {
            // Small n, max l/t
            let n = rng.gen_range_i64(1, 100);
            let l = rng.gen_range_i64(1, 1_000_000_000);
            let t = rng.gen_range_i64(1, 1_000_000_000);
            let tasks = (n + 6) / 7;
            let max_p = (n * l + tasks * t).min(10_000_000_000_000_000);
            let p = rng.gen_range_i64(1, max_p);
            (n, p, l, t)
        }
        2 => {
            // p exactly equal to max
            let n = rng.gen_range_i64(1, 100_000_000);
            let l = rng.gen_range_i64(1, 1_000_000_000);
            let t = rng.gen_range_i64(1, 1_000_000_000);
            let tasks = (n + 6) / 7;
            let max_p = (n * l + tasks * t).min(10_000_000_000_000_000);
            (n, max_p, l, t)
        }
        3 => {
            // p = 1
            let n = rng.gen_range_i64(1, 100_000_000);
            let l = rng.gen_range_i64(1, 1_000_000_000);
            let t = rng.gen_range_i64(1, 1_000_000_000);
            (n, 1, l, t)
        }
        4 => {
            // n is multiple of 7
            let n = (rng.gen_range_i64(1, 14_285_714)) * 7;
            let l = rng.gen_range_i64(1, 1_000_000_000);
            let t = rng.gen_range_i64(1, 1_000_000_000);
            let tasks = (n + 6) / 7;
            let max_p = (n * l + tasks * t).min(10_000_000_000_000_000);
            let p = rng.gen_range_i64(1, max_p);
            (n, p, l, t)
        }
        _ => {
            let n = rng.gen_range_i64(1, 100_000_000);
            let l = rng.gen_range_i64(1, 1_000_000_000);
            let t = rng.gen_range_i64(1, 1_000_000_000);
            let tasks = (n + 6) / 7;
            let max_p = (n * l + tasks * t).min(10_000_000_000_000_000);
            let p = rng.gen_range_i64(1, max_p);
            (n, p, l, t)
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
        let q: usize = if count < 30 { rng.gen_range_usize(20, 50) } else { rng.gen_range_usize(30, 100) };
        let mut cases: Vec<Case> = Vec::new();
        for _ in 0..q {
            cases.push(pick_adv(&mut rng));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|&c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

