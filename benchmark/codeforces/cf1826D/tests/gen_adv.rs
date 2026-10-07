use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (b: Vec<i32>)
    requires
        3 <= vals.len() <= 100_000,
        forall|j: int| #![trigger vals[j]] 0 <= j && j < vals.len() ==> 1 <= vals[j] as int && vals[j] as int <= 100_000_000,
    ensures
        3 <= b.len() <= 100_000,
        forall|j: int| #![trigger b[j]] 0 <= j && j < b.len() ==> 1 <= b[j] as int && b[j] as int <= 100_000_000,
{
    let n = vals.len();
    let mut b: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == vals.len(),
            b.len() == i,
            forall|j: int| #![trigger vals[j]] 0 <= j && j < vals.len() ==> 1 <= vals[j] as int && vals[j] as int <= 100_000_000,
            forall|k: int| #![trigger b[k]] 0 <= k && k < i as int ==> 1 <= b[k] as int && b[k] as int <= 100_000_000,
        decreases n - i,
    {
        b.push(vals[i]);
        i = i + 1;
    }
    b
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

fn random_array(rng: &mut Rng, len: usize, max_v: i32) -> Vec<i32> {
    (0..len).map(|_| rng.gen_range_i64(1, max_v as i64) as i32).collect()
}

fn build_input(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for b in cases {
        s.push_str(&format!("{}\n", b.len()));
        let parts: Vec<String> = b.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Single big test entries
    let big_singles: Vec<Vec<i32>> = vec![
        // All max
        (0..1000).map(|_| 100_000_000i32).collect(),
        // All min
        (0..1000).map(|_| 1i32).collect(),
        // Strictly ascending
        (0..1000).map(|i| (i + 1) as i32).collect(),
        // Strictly descending
        (0..1000).map(|i| (1000 - i) as i32).collect(),
        // Saw-tooth pattern
        (0..1000).map(|i| if i % 2 == 0 {100_000_000i32} else {1}).collect(),
    ];
    for case in &big_singles {
        if count >= target { break; }
        let cases = vec![case.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|b| Solution::best_running_miles(b)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    // Generate adversarial bundled batches
    while count < target {
        let mode = rng.next_u64() % 5;
        let mut cases: Vec<Vec<i32>> = Vec::new();
        let mut total_n = 0usize;
        match mode {
            0 => {
                // Many small cases
                let t = rng.gen_range_usize(20, 50);
                for _ in 0..t {
                    let len = rng.gen_range_usize(3, 20);
                    if total_n + len > 100_000 { break; }
                    total_n += len;
                    cases.push(random_array(&mut rng, len, 100_000_000));
                }
            }
            1 => {
                // Few large cases
                let t = rng.gen_range_usize(2, 5);
                for _ in 0..t {
                    let len = rng.gen_range_usize(1000, 10_000);
                    if total_n + len > 100_000 { break; }
                    total_n += len;
                    cases.push(random_array(&mut rng, len, 100_000_000));
                }
            }
            2 => {
                // One huge case
                let len = rng.gen_range_usize(50_000, 100_000);
                cases.push(random_array(&mut rng, len, 100_000_000));
            }
            3 => {
                // Mix of patterns
                let t = rng.gen_range_usize(5, 20);
                for _ in 0..t {
                    let len = rng.gen_range_usize(3, 100);
                    if total_n + len > 100_000 { break; }
                    total_n += len;
                    let pattern = rng.next_u64() % 4;
                    let arr: Vec<i32> = match pattern {
                        0 => (0..len).map(|_| 1).collect(),
                        1 => (0..len).map(|_| 100_000_000).collect(),
                        2 => (0..len).map(|i| (i + 1) as i32).collect(),
                        _ => random_array(&mut rng, len, 100_000_000),
                    };
                    cases.push(arr);
                }
            }
            _ => {
                // Random mid-size
                let t = rng.gen_range_usize(5, 30);
                for _ in 0..t {
                    let len = rng.gen_range_usize(3, 500);
                    if total_n + len > 100_000 { break; }
                    total_n += len;
                    cases.push(random_array(&mut rng, len, 100_000_000));
                }
            }
        }
        if cases.is_empty() { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|b| Solution::best_running_miles(b)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

