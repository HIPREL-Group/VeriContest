use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (a: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> #[trigger] values[i] == 0 || values[i] == 1,
    ensures
        1 <= a.len() <= 100,
        forall|j: int| 0 <= j < a.len() ==> #[trigger] a[j] == 0 || a[j] == 1,
{
    let n = values.len();
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            a.len() == i,
            forall|k: int| 0 <= k < values.len() ==> #[trigger] values[k] == 0 || values[k] == 1,
            forall|k: int| 0 <= k < i as int ==> #[trigger] a[k] == values[k],
        decreases n - i,
    {
        a.push(values[i]);
        i = i + 1;
    }
    a
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

fn random_binary(rng: &mut Rng, len: usize, p_one: u32) -> Vec<i32> {
    (0..len).map(|_| if (rng.next_u64() % 100) < p_one as u64 {1i32} else {0}).collect()
}

fn build_input(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
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

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Big single-cases
    let big_singles: Vec<Vec<i32>> = vec![
        vec![0; 100],
        vec![1; 100],
        // Single 1 in middle
        { let mut v = vec![0; 100]; v[50] = 1; v },
        // Single 0 in middle
        { let mut v = vec![1; 100]; v[50] = 0; v },
        // Alternating
        (0..100).map(|i| (i % 2) as i32).collect(),
    ];
    for c in &big_singles {
        if count >= target { break; }
        let cases = vec![c.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|a| Solution::longest_blank_space(a)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    // Adversarial bundles: max t = 1000, max n = 100
    while count < target {
        let mode = rng.next_u64() % 5;
        let mut cases: Vec<Vec<i32>> = Vec::new();
        match mode {
            0 => {
                // Many short
                let t = rng.gen_range_usize(50, 200);
                for _ in 0..t {
                    let n = rng.gen_range_usize(1, 20);
                    cases.push(random_binary(&mut rng, n, 50));
                }
            }
            1 => {
                // Few large (n=100)
                let t = rng.gen_range_usize(5, 30);
                for _ in 0..t {
                    cases.push(random_binary(&mut rng, 100, 50));
                }
            }
            2 => {
                // Boundary: max t with max n
                let t = rng.gen_range_usize(100, 500);
                for _ in 0..t {
                    let n = rng.gen_range_usize(50, 100);
                    let p = (rng.next_u64() % 95 + 2) as u32;
                    cases.push(random_binary(&mut rng, n, p));
                }
            }
            3 => {
                // Patterns
                let t = rng.gen_range_usize(10, 50);
                for _ in 0..t {
                    let n = rng.gen_range_usize(10, 100);
                    let pat = rng.next_u64() % 4;
                    let arr: Vec<i32> = match pat {
                        0 => vec![0; n],
                        1 => vec![1; n],
                        2 => (0..n).map(|i| (i % 2) as i32).collect(),
                        _ => random_binary(&mut rng, n, 30),
                    };
                    cases.push(arr);
                }
            }
            _ => {
                let t = rng.gen_range_usize(20, 100);
                for _ in 0..t {
                    let n = rng.gen_range_usize(1, 100);
                    let p = (rng.next_u64() % 95 + 2) as u32;
                    cases.push(random_binary(&mut rng, n, p));
                }
            }
        }
        if cases.is_empty() { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|a| Solution::longest_blank_space(a)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

