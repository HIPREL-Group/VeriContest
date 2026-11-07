use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_n: i64, seed_l: i64, seed_t: i64, seed_p: i64, mutation_kind: u8,
) -> (result: (i64, i64, i64, i64))
    requires
        1 <= seed_n <= 100_000_000,
        1 <= seed_l <= 1_000_000_000,
        1 <= seed_t <= 1_000_000_000,
        1 <= seed_p <= 10_000_000_000_000_000,
    ensures
        1 <= result.0 <= 100_000_000,
        1 <= result.1 <= 10_000_000_000_000_000,
        1 <= result.2 <= 1_000_000_000,
        1 <= result.3 <= 1_000_000_000,
        ((result.0 + 6) / 7 / 2) * (result.2 + 2 * result.3) <= 9_000_000_000_000_000_000,
        result.1 <= result.0 * result.2 + ((result.0 + 6) / 7) * result.3,
{
    let mut n = seed_n;
    let mut l = seed_l;
    let mut t = seed_t;

    if mutation_kind == 0 {
        // identity
    } else if mutation_kind == 1 && seed_n < 100_000_000 {
        n = seed_n + 1;
    } else if mutation_kind == 2 && seed_n > 1 {
        n = seed_n - 1;
    } else if mutation_kind == 3 && seed_l < 1_000_000_000 {
        l = seed_l + 1;
    } else if mutation_kind == 4 && seed_l > 1 {
        l = seed_l - 1;
    } else if mutation_kind == 5 && seed_t < 1_000_000_000 {
        t = seed_t + 1;
    } else if mutation_kind == 6 && seed_t > 1 {
        t = seed_t - 1;
    } else if mutation_kind == 7 {
        n = 1;
    } else if mutation_kind == 8 {
        n = 100_000_000;
    } else if mutation_kind == 9 {
        l = 1;
    } else if mutation_kind == 10 {
        l = 1_000_000_000;
    } else if mutation_kind == 11 {
        t = 1;
    } else if mutation_kind == 12 {
        t = 1_000_000_000;
    } else if mutation_kind == 13 {
        n = 1; l = 1; t = 1;
    } else if mutation_kind == 14 {
        n = 100_000_000; l = 1_000_000_000; t = 1_000_000_000;
    } else if mutation_kind == 15 {
        let hn = seed_n / 2;
        n = if hn >= 1 { hn } else { 1 };
    } else if mutation_kind == 16 {
        let hl = seed_l / 2;
        l = if hl >= 1 { hl } else { 1 };
    } else if mutation_kind == 17 {
        let ht = seed_t / 2;
        t = if ht >= 1 { ht } else { 1 };
    } else {
        // fallback: identity
    }

    // n in [1, 100_000_000], l in [1, 1_000_000_000], t in [1, 1_000_000_000]

    let tasks: i64 = (n + 6) / 7;

    // Prove overflow safety for n * l
    assert(n as int * l as int <= 100_000_000 * 1_000_000_000) by(nonlinear_arith)
        requires n <= 100_000_000, l <= 1_000_000_000, n >= 1, l >= 1;
    let nl: i64 = n * l;

    // tasks = (n + 6) / 7, with n <= 100_000_000, so tasks <= 14_285_715
    proof {
        assert(n + 6 <= 100_000_006) by(nonlinear_arith)
            requires 1 <= n <= 100_000_000;
        assert((n + 6) as int / 7 <= 100_000_006int / 7) by(nonlinear_arith)
            requires n + 6 <= 100_000_006, n >= 1;
    }

    assert(tasks as int * t as int <= 14_285_715 * 1_000_000_000) by(nonlinear_arith)
        requires tasks <= 14_285_715, t <= 1_000_000_000, tasks >= 0, t >= 1;
    let tt: i64 = tasks * t;

    // nl + tt overflow safety
    assert(nl as int + tt as int <= 114_285_715_000_000_000) by(nonlinear_arith)
        requires
            nl as int <= 100_000_000 * 1_000_000_000,
            tt as int <= 14_285_715 * 1_000_000_000;
    let max_p: i64 = nl + tt;

    // max_p >= 1 since nl >= 1
    assert(nl >= 1) by(nonlinear_arith)
        requires nl == n * l, n >= 1, l >= 1;
    let p_clamped = if seed_p <= max_p { seed_p } else { max_p };
    let p = if p_clamped <= 10_000_000_000_000_000 { p_clamped } else { 10_000_000_000_000_000 };

    // Prove constraint 5: pairs * (l + 2*t) <= 9e18
    let pairs: i64 = tasks / 2;
    proof {
        assert(tasks as int / 2 <= 14_285_715int / 2) by(nonlinear_arith)
            requires tasks <= 14_285_715, tasks >= 0;
    }
    assert(pairs as int * (l as int + 2 * t as int) <= 7_142_857 * 3_000_000_000) by(nonlinear_arith)
        requires pairs <= 7_142_857, l <= 1_000_000_000, t <= 1_000_000_000, pairs >= 0, l >= 1, t >= 1;
    assert(7_142_857 * 3_000_000_000 <= 9_000_000_000_000_000_000int);

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

type Case = (i64, i64, i64, i64); // (n, p, l, t)

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

// Generate valid case: p must be <= n*l + tasks*t
fn random_case(rng: &mut Rng) -> Case {
    let n = rng.gen_range_i64(1, 100_000_000);
    let l = rng.gen_range_i64(1, 1_000_000_000);
    let t = rng.gen_range_i64(1, 1_000_000_000);
    let tasks = (n + 6) / 7;
    let max_p = n * l + tasks * t;
    let max_p = if max_p > 10_000_000_000_000_000 { 10_000_000_000_000_000 } else { max_p };
    let p = rng.gen_range_i64(1, max_p);
    (n, p, l, t)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1902);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Reasonable example cases (since description doesn't show specific examples)
    let example: Vec<Case> = vec![
        (28, 100, 5, 7),  // 28 days = 4 tasks
        (7, 5, 5, 7),     // 1 task
        (14, 17, 1, 100), // 2 tasks, low l, high t
    ];
    {
        let inp = build_input(&example);
        let answers: Vec<i64> = example.iter().map(|&c| solve(c)).collect();
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Edge cases
    let edges: Vec<Case> = vec![
        (1, 1, 1, 1),
        (1, 2, 1, 1),
        (7, 1, 1, 1),
        (7, 7, 1, 0_i64.max(1)),
        (100_000_000, 100, 1, 1),
        (100_000_000, 1_000_000_000_000_000, 1_000_000_000, 1_000_000_000),
    ];
    for &ec in &edges {
        if count >= target { break; }
        let cases = vec![ec];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|&c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let q: usize = if count < 30 { rng.gen_range_usize(2, 8) } else { rng.gen_range_usize(5, 30) };
        let mut cases: Vec<Case> = Vec::new();
        for _ in 0..q {
            cases.push(random_case(&mut rng));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|&c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

