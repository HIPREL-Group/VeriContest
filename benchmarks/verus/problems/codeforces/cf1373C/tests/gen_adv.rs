use vstd::prelude::*;

verus! {

pub fn generate_test_case(bits: &Vec<bool>) -> (deltas: Vec<i32>)
    requires
        1 <= bits.len() <= 1_000_000,
    ensures
        deltas.len() == bits.len(),
        1 <= deltas.len() <= 1_000_000,
        forall|j: int| 0 <= j < deltas@.len() ==> (deltas[j] == 1i32 || deltas[j] == -1i32),
{
    let n = bits.len();
    let mut deltas: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == bits.len(),
            0 <= i <= n,
            deltas.len() == i,
            forall|j: int| 0 <= j < i as int ==> (deltas[j] == 1i32 || deltas[j] == -1i32),
        decreases n - i,
    {
        if bits[i] {
            deltas.push(1i32);
        } else {
            deltas.push(-1i32);
        }
        i = i + 1;
    }
    deltas
}

}

use std::io::Write;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
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

fn random_str(rng: &mut Rng, n: usize, p_minus_pct: u32) -> String {
    let mut s = String::with_capacity(n);
    for _ in 0..n {
        if (rng.next_u64() % 100) < p_minus_pct as u64 { s.push('-'); } else { s.push('+'); }
    }
    s
}

fn build_input(strs: &[String]) -> String {
    let mut s = format!("{}\n", strs.len());
    for st in strs {
        s.push_str(st);
        s.push('\n');
    }
    s
}

fn solve(s: &str) -> i64 {
    let deltas: Vec<i32> = s.chars().map(|c| if c == '+' { 1 } else { -1 }).collect();
    Solution::pluses_minuses_total_steps(deltas)
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
    let mut rng = Rng::new(31337);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    let mut count = 0usize;

    // boundary
    {
        let strs: Vec<String> = vec!["+".to_string(), "-".to_string(), "++".to_string(), "--".to_string()];
        let answers: Vec<i64> = strs.iter().map(|s| solve(s)).collect();
        let inp = build_input(&strs);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    // single all-minus large
    {
        let strs: Vec<String> = vec!["-".repeat(10000)];
        let answers: Vec<i64> = strs.iter().map(|s| solve(s)).collect();
        let inp = build_input(&strs);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = match count % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 5),
            2 => rng.gen_range_usize(5, 15),
            3 => rng.gen_range_usize(15, 30),
            _ => rng.gen_range_usize(30, 50),
        };
        let mut strs: Vec<String> = Vec::new();
        let mut total: usize = 0;
        let cap = 50000usize;
        for _ in 0..t {
            let n = match rng.next_u64() % 5 {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(1, 50),
                2 => rng.gen_range_usize(50, 500),
                3 => rng.gen_range_usize(500, 5000),
                _ => rng.gen_range_usize(1, 100),
            };
            if total + n > cap { break; }
            total += n;
            let pct = match rng.next_u64() % 5 {
                0 => 90,
                1 => 70,
                2 => 50,
                3 => 30,
                _ => 10,
            };
            strs.push(random_str(&mut rng, n, pct));
        }
        if strs.is_empty() { continue; }
        let answers: Vec<i64> = strs.iter().map(|s| solve(s)).collect();
        let inp = build_input(&strs);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

