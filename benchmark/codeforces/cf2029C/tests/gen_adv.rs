use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: &Vec<i32>) -> (res: Vec<i32>)
    requires
        1 <= seed_a.len() <= 300_000,
        forall|i: int| 0 <= i < seed_a.len() ==>
            1 <= (#[trigger] seed_a[i]) <= seed_a.len() as int,
    ensures
        1 <= res.len() <= 300_000,
        forall|i: int| 0 <= i < res.len() ==>
            1 <= (#[trigger] res[i]) <= res.len() as int,
{
    let n = seed_a.len();
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == seed_a.len(),
            1 <= n <= 300_000,
            0 <= i <= n,
            a.len() == i,
            forall|j: int| 0 <= j < seed_a.len() ==>
                1 <= (#[trigger] seed_a[j]) <= seed_a.len() as int,
            forall|j: int| 0 <= j < i as int ==>
                1 <= (#[trigger] a[j]) <= n as int,
        decreases n - i,
    {
        a.push(seed_a[i]);
        i = i + 1;
    }
    a
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
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn make_seed_arr(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // n=1
            vec![1]
        }
        1 => {
            // strictly increasing
            let n = rng.gen_range_usize(2, 100);
            (1..=n as i32).collect()
        }
        2 => {
            // strictly decreasing
            let n = rng.gen_range_usize(2, 100);
            (1..=n as i32).rev().collect()
        }
        3 => {
            // all equal
            let n = rng.gen_range_usize(1, 100);
            let v = rng.gen_range_i64(1, n.max(1) as i64) as i32;
            vec![v; n]
        }
        4 => {
            // small alphabet
            let n = rng.gen_range_usize(1, 100);
            (0..n).map(|_| rng.gen_range_i64(1, 3.min(n as i64).max(1)) as i32).collect()
        }
        5 => {
            // larger n
            let n = rng.gen_range_usize(100, 500);
            (0..n).map(|_| rng.gen_range_i64(1, n as i64) as i32).collect()
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            (0..n).map(|_| rng.gen_range_i64(1, n as i64) as i32).collect()
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
    let modes = 7usize;

    while count < target {
        let t: usize = if count < 20 { 1 }
                       else if count < 80 { rng.gen_range_usize(2, 6) }
                       else if count < 150 { rng.gen_range_usize(3, 12) }
                       else { rng.gen_range_usize(5, 25) };
        let mut cases: Vec<Vec<i32>> = Vec::new();
        let mut total = 0usize;
        for sub in 0..t {
            let mode = (count + sub) % modes;
            let seed = make_seed_arr(&mut rng, mode);
            // Pass through verified function
            let a = generate_test_case(&seed);
            if total + a.len() > 10_000 { break; }
            total += a.len();
            cases.push(a);
        }
        if cases.is_empty() { continue; }
        let answers: Vec<i32> = cases.iter().map(|a| Solution::max_rating(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
