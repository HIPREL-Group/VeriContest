use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: Vec<i64>) -> (result: Vec<i64>)
    requires
        2 <= seed_a.len() <= 200_000,
        forall|i: int| 0 <= i < seed_a.len() ==> 1 <= #[trigger] seed_a[i] && seed_a[i] <= 1_000_000_000,
    ensures
        2 <= result.len() <= 200_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] && result[i] <= 1_000_000_000,
{
    seed_a
}

} // verus!

use std::io::Write;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
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
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn gen_arr(rng: &mut Rng, mode: usize) -> Vec<i64> {
    match mode {
        0 => {
            let a = rng.gen_range_i64(1, 1_000_000_000);
            let b = rng.gen_range_i64(1, 1_000_000_000);
            vec![a, b]
        }
        1 => {
            let n = rng.gen_range_usize(2, 30);
            let v = rng.gen_range_i64(1, 1_000_000_000);
            vec![v; n]
        }
        2 => {
            let n = rng.gen_range_usize(2, 30);
            (1..=n as i64).map(|x| x * rng.gen_range_i64(1, 100)).collect()
        }
        3 => {
            let n = rng.gen_range_usize(2, 30);
            (1..=n as i64).rev().map(|x| x * rng.gen_range_i64(1, 100)).collect()
        }
        4 => {
            let n = rng.gen_range_usize(100, 300);
            (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect()
        }
        5 => {
            let n = rng.gen_range_usize(2, 30);
            let mut a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 100)).collect();
            *a.last_mut().unwrap() = rng.gen_range_i64(1_000_000_000 - 100, 1_000_000_000);
            a
        }
        6 => {
            let n = rng.gen_range_usize(3, 30);
            let mut a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 100)).collect();
            a[n-2] = rng.gen_range_i64(1_000_000_000 - 100, 1_000_000_000);
            a
        }
        _ => {
            let n = rng.gen_range_usize(2, 100);
            (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect()
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;
    let modes = 8usize;

    while count < target {
        let t: usize = if count < 20 { 1 }
                       else if count < 80 { rng.gen_range_usize(2, 6) }
                       else if count < 150 { rng.gen_range_usize(3, 15) }
                       else { rng.gen_range_usize(5, 25) };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        let mut total_n = 0usize;
        for sub in 0..t {
            let mode = (count * 7 + sub) % modes;
            let seed_a = gen_arr(&mut rng, mode);
            if total_n + seed_a.len() > 5000 { break; }
            total_n += seed_a.len();
            let a = generate_test_case(seed_a);
            cases.push(a);
        }
        if cases.is_empty() { continue; }
        let answers: Vec<i64> = cases.iter().map(|a| Solution::battle_for_survive(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
