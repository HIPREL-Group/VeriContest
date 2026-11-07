use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    first_val: i64,
    rest: &Vec<i64>,
) -> (c: Vec<i64>)
    requires
        1 <= first_val <= 1_000_000_000,
        rest.len() <= 199_999,
        forall|i: int| 0 <= i < rest.len() ==> 0 <= #[trigger] rest[i] <= 1_000_000_000,
    ensures
        1 <= c.len() <= 200_000,
        forall|i: int| 0 <= i < c.len() as int ==> 0 <= #[trigger] c[i] as int <= 1_000_000_000,
        c[0] as int >= 1,
{
    let mut c: Vec<i64> = Vec::new();
    c.push(first_val);
    let mut i: usize = 0;
    while i < rest.len()
        invariant
            c.len() == i + 1,
            i <= rest.len(),
            rest.len() <= 199_999,
            1 <= first_val <= 1_000_000_000,
            c[0] as int == first_val as int,
            forall|k: int| 0 <= k < rest.len() ==> 0 <= #[trigger] rest[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < c.len() as int ==> 0 <= #[trigger] c[k] as int <= 1_000_000_000,
        decreases rest.len() - i,
    {
        c.push(rest[i]);
        i = i + 1;
    }
    c
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

fn build_input(cases: &[Vec<i64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for c in cases {
        s.push_str(&format!("{}\n", c.len()));
        let p: Vec<String> = c.iter().map(|x| x.to_string()).collect();
        s.push_str(&p.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn random_case(rng: &mut Rng, n: usize, max_v: i64) -> Vec<i64> {
    let mut c: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(0, max_v)).collect();
    if c[0] < 1 { c[0] = 1; }
    c
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Big single
    let big_singles: Vec<Vec<i64>> = vec![
        vec![1_000_000_000; 100_000],
        (1..=100_000).collect::<Vec<i64>>(),
        (1..=100_000).rev().collect::<Vec<i64>>(),
        vec![1; 100_000],
    ];
    for ec in &big_singles {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| Solution::min_chip_teleports(c.clone())).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let mode = rng.next_u64() % 4;
        let mut cases: Vec<Vec<i64>> = Vec::new();
        let mut total_n = 0usize;
        match mode {
            0 => {
                let t = rng.gen_range_usize(20, 100);
                for _ in 0..t {
                    let n = rng.gen_range_usize(1, 30);
                    if total_n + n > 200_000 { break; }
                    total_n += n;
                    cases.push(random_case(&mut rng, n, 1_000_000_000));
                }
            }
            1 => {
                let t = rng.gen_range_usize(2, 5);
                for _ in 0..t {
                    let n = rng.gen_range_usize(5000, 30_000);
                    if total_n + n > 200_000 { break; }
                    total_n += n;
                    cases.push(random_case(&mut rng, n, 1_000_000_000));
                }
            }
            2 => {
                let n = rng.gen_range_usize(50_000, 100_000);
                cases.push(random_case(&mut rng, n, 1_000_000_000));
            }
            _ => {
                let t = rng.gen_range_usize(5, 30);
                for _ in 0..t {
                    let n = rng.gen_range_usize(1, 1000);
                    if total_n + n > 200_000 { break; }
                    total_n += n;
                    cases.push(random_case(&mut rng, n, 1_000_000_000));
                }
            }
        }
        if cases.is_empty() { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| Solution::min_chip_teleports(c.clone())).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

