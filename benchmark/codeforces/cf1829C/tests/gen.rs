use vstd::prelude::*;

verus! {

pub open spec fn valid_mask(x: i32) -> bool {
    0 <= x <= 3
}

pub fn generate_test_case(m: Vec<i32>, s: Vec<i32>, mutation_kind: u8) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= m.len() <= 200_000,
        m.len() == s.len(),
        forall|i: int| 0 <= i < m.len() ==> 1 <= #[trigger] m[i] <= 200_000,
        forall|i: int| 0 <= i < s.len() ==> valid_mask(#[trigger] s[i]),
    ensures
        1 <= result.0.len() <= 200_000,
        result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 200_000,
        forall|i: int| 0 <= i < result.1.len() ==> valid_mask(#[trigger] result.1[i]),
{
    if mutation_kind == 0 {
        // identity
        (m, s)
    } else if mutation_kind == 1 {
        // set first s to 3 (both skills in one book)
        let mut s2 = s;
        s2.set(0, 3);
        (m, s2)
    } else if mutation_kind == 2 && m.len() >= 2 {
        // set first s to 2, second s to 1 (pair coverage)
        let mut s2 = s;
        s2.set(0, 2);
        s2.set(1, 1);
        (m, s2)
    } else if mutation_kind == 3 && m[0] < 200_000 {
        // nudge first m up
        let mut m2 = m;
        m2.set(0, m2[0] + 1);
        (m2, s)
    } else if mutation_kind == 4 && m[0] > 1 {
        // nudge first m down
        let mut m2 = m;
        m2.set(0, m2[0] - 1);
        (m2, s)
    } else if mutation_kind == 5 {
        // set all s to 0 (impossible case — no skills)
        let mut s2 = s;
        let mut i: usize = 0;
        while i < s2.len()
            invariant
                0 <= i <= s2.len(),
                s2.len() == m.len(),
                1 <= s2.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> s2[j] == 0i32,
                forall|j: int| 0 <= j < m.len() ==> 1 <= #[trigger] m[j] <= 200_000,
            decreases s2.len() - i,
        {
            s2.set(i, 0);
            i += 1;
        }
        (m, s2)
    } else if mutation_kind == 6 {
        // set first m to 1 (minimum time)
        let mut m2 = m;
        m2.set(0, 1);
        (m2, s)
    } else if mutation_kind == 7 {
        // set first m to 200_000 (maximum time)
        let mut m2 = m;
        m2.set(0, 200_000);
        (m2, s)
    } else {
        // fallback — identity
        (m, s)
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

fn mask_to_bits(mask: i32) -> &'static str {
    match mask {
        3 => "11",
        2 => "10",
        1 => "01",
        _ => "00",
    }
}

// Build input from list of (m, s_mask) pairs per case
fn build_input(cases: &[Vec<(i32, i32)>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for c in cases {
        s.push_str(&format!("{}\n", c.len()));
        for &(m, mask) in c {
            s.push_str(&format!("{} {}\n", m, mask_to_bits(mask)));
        }
    }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn random_case(rng: &mut Rng, n: usize, max_m: i32) -> Vec<(i32, i32)> {
    (0..n).map(|_| {
        let m = rng.gen_range_i64(1, max_m as i64) as i32;
        let mask = (rng.next_u64() % 4) as i32;
        (m, mask)
    }).collect()
}

fn solve(case: &[(i32, i32)]) -> i32 {
    let m: Vec<i32> = case.iter().map(|&(m, _)| m).collect();
    let s: Vec<i32> = case.iter().map(|&(_, s)| s).collect();
    Solution::min_minutes(m, s)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1829);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Hand-crafted small examples (description had concatenated input that's hard to disentangle)
    let example: Vec<Vec<(i32, i32)>> = vec![
        vec![(2, 0), (3, 2), (4, 1), (4, 0)],   // 3+4=7
        vec![(3, 1), (3, 1), (5, 1), (2, 2)],   // 3+2=5
        vec![(5, 3)],                            // 5
        vec![(10, 0), (3, 1), (4, 2)],           // 3+4=7
        vec![(1, 1)],                            // -1 (no skill 1)
        vec![(5, 3), (3, 3), (8, 1), (7, 2)],   // min(5,3,7+8)=3
    ];
    {
        let inp = build_input(&example);
        let answers: Vec<i32> = example.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Single-test edge cases
    let edge_cases: Vec<Vec<(i32, i32)>> = vec![
        vec![(1, 3)],                       // single book with both skills
        vec![(1, 0)],                       // single book with no skills
        vec![(1, 1), (1, 2)],               // both skills via separate
        vec![(5, 1)],                       // only one skill possible
        vec![(1, 1), (1, 1)],               // only skill 1, twice
        vec![(200000, 3)],                  // max m
    ];
    for ec in &edge_cases {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    // Bundled multi-test
    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(2, 6) } else { rng.gen_range_usize(3, 15) };
        let mut cases: Vec<Vec<(i32, i32)>> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 50);
            if total_n + n > 200_000 { break; }
            total_n += n;
            cases.push(random_case(&mut rng, n, 200_000));
        }
        if cases.is_empty() { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

