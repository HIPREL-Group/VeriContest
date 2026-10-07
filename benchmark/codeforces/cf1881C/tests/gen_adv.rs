use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, fillers: &Vec<i64>) -> (res: (usize, Vec<i64>))
    requires
        2 <= n <= 1000,
        n % 2 == 0,
        fillers.len() == n * n,
        forall|k: int| 0 <= k < fillers.len() ==> 0 <= (#[trigger] fillers[k] as int) <= 25,
    ensures
        2 <= (res.0 as int) <= 1000,
        (res.0 as int) % 2 == 0,
        (res.1.len() as int) == (res.0 as int) * (res.0 as int),
        forall|k: int| 0 <= k < (res.1.len() as int) ==> 0 <= (#[trigger] res.1[k] as int) && (res.1[k] as int) <= 25,
{
    let mut grid: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let total: usize = n * n;
    while i < total
        invariant
            2 <= n <= 1000,
            n % 2 == 0,
            fillers.len() == n * n,
            total == n * n,
            0 <= i <= total,
            grid.len() == i,
            forall|k: int| 0 <= k < fillers.len() ==> 0 <= (#[trigger] fillers[k] as int) <= 25,
            forall|k: int| 0 <= k < grid.len() ==> 0 <= (#[trigger] grid[k] as int) <= 25,
        decreases total - i,
    {
        let v = fillers[i];
        grid.push(v);
        i = i + 1;
    }
    (n, grid)
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

type Case = (usize, Vec<String>);

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, rows) in cases {
        s.push_str(&format!("{}\n", n));
        for r in rows {
            s.push_str(r);
            s.push('\n');
        }
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn solve(c: &Case) -> i64 {
    let mut grid: Vec<i64> = Vec::with_capacity(c.0 * c.0);
    for r in &c.1 {
        for ch in r.chars() {
            grid.push((ch as u8 - b'a') as i64);
        }
    }
    Solution::min_ops_perfect_square(c.0, grid)
}

fn random_case(rng: &mut Rng, n: usize, alphabet_size: u8) -> Case {
    let rows: Vec<String> = (0..n).map(|_| {
        let s: String = (0..n).map(|_| {
            (b'a' + (rng.gen_range_i64(0, alphabet_size as i64 - 1) as u8)) as char
        }).collect();
        s
    }).collect();
    (n, rows)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Big single (n = 1000 since sum of n <= 10^3)
    let big_singles: Vec<Case> = vec![
        (1000, (0..1000).map(|_| "a".repeat(1000)).collect()),  // all same: 0
        (1000, (0..1000).map(|_| "z".repeat(1000)).collect()),  // all max: 0
        (998, (0..998).map(|_| {
            let s: String = (0..998).map(|j| (b'a' + (j % 26) as u8) as char).collect(); s
        }).collect()),
    ];
    for ec in &big_singles {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let mode = rng.next_u64() % 4;
        let mut cases: Vec<Case> = Vec::new();
        let mut total_n = 0usize;
        match mode {
            0 => {
                // Many small n
                let t = rng.gen_range_usize(20, 50);
                for _ in 0..t {
                    let n = (rng.gen_range_usize(1, 5)) * 2;
                    if total_n + n > 1000 { break; }
                    total_n += n;
                    cases.push(random_case(&mut rng, n, 26));
                }
            }
            1 => {
                // Few medium
                let t = rng.gen_range_usize(2, 10);
                for _ in 0..t {
                    let n = (rng.gen_range_usize(10, 50)) * 2;
                    if total_n + n > 1000 { break; }
                    total_n += n;
                    cases.push(random_case(&mut rng, n, 26));
                }
            }
            2 => {
                // One big
                let n = (rng.gen_range_usize(200, 500)) * 2;
                if n > 1000 { continue; }
                cases.push(random_case(&mut rng, n, 26));
            }
            _ => {
                // Mixed alphabets
                let t = rng.gen_range_usize(2, 10);
                for _ in 0..t {
                    let n = (rng.gen_range_usize(1, 30)) * 2;
                    if total_n + n > 1000 { break; }
                    total_n += n;
                    let alpha = (rng.gen_range_usize(2, 26)) as u8;
                    cases.push(random_case(&mut rng, n, alpha));
                }
            }
        }
        if cases.is_empty() { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

