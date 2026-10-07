use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_s: &Vec<i32>,
    seed_m: usize,
    seed_k: usize,
) -> (res: (Vec<i32>, usize, usize))
    requires
        1 <= seed_s.len() <= 200_000,
        1 <= (seed_m as int) <= seed_s.len() as int,
        1 <= (seed_k as int) <= seed_s.len() as int,
        forall|t: int| 0 <= t < seed_s.len() as int ==>
            (#[trigger] seed_s[t] == 0 || seed_s[t] == 1),
    ensures
        1 <= res.0.len() <= 200_000,
        1 <= (res.1 as int) <= res.0.len() as int,
        1 <= (res.2 as int) <= res.0.len() as int,
        forall|t: int| 0 <= t < res.0.len() as int ==>
            (#[trigger] res.0[t] == 0 || res.0[t] == 1),
{
    let n = seed_s.len();
    let mut s: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == seed_s.len(),
            1 <= n <= 200_000,
            0 <= i <= n,
            s.len() == i,
            forall|t: int| 0 <= t < seed_s.len() as int ==>
                (#[trigger] seed_s[t] == 0 || seed_s[t] == 1),
            forall|t: int| 0 <= t < i as int ==>
                (#[trigger] s[t] == 0 || s[t] == 1),
        decreases n - i,
    {
        s.push(seed_s[i]);
        i = i + 1;
    }
    (s, seed_m, seed_k)
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

fn build_input(cases: &[(Vec<i32>, usize, usize)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, m, k) in cases {
        let n = a.len();
        s.push_str(&format!("{} {} {}\n", n, m, k));
        let mut row = String::with_capacity(n);
        for &v in a {
            row.push(if v == 1 { '1' } else { '0' });
        }
        row.push('\n');
        s.push_str(&row);
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

fn make_seed_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, usize, usize) {
    match mode {
        0 => {
            // all zeros, k small
            let n = rng.gen_range_usize(2, 100);
            let m = rng.gen_range_usize(1, n);
            let k = rng.gen_range_usize(1, n);
            (vec![0; n], m, k)
        }
        1 => {
            // all ones
            let n = rng.gen_range_usize(2, 100);
            let m = rng.gen_range_usize(1, n);
            let k = rng.gen_range_usize(1, n);
            (vec![1; n], m, k)
        }
        2 => {
            // alternating
            let n = rng.gen_range_usize(2, 100);
            let m = rng.gen_range_usize(1, n);
            let k = rng.gen_range_usize(1, n);
            ((0..n).map(|i| if i % 2 == 0 { 1 } else { 0 }).collect(), m, k)
        }
        3 => {
            // long zeros runs
            let n = rng.gen_range_usize(10, 200);
            let m = rng.gen_range_usize(1, 5.min(n));
            let k = rng.gen_range_usize(1, m);
            (vec![0; n], m, k)
        }
        4 => {
            // ones at boundaries, zeros in middle
            let n = rng.gen_range_usize(10, 100);
            let m = rng.gen_range_usize(1, n);
            let k = rng.gen_range_usize(1, n);
            let mut s: Vec<i32> = vec![0; n];
            s[0] = 1;
            s[n-1] = 1;
            (s, m, k)
        }
        5 => {
            // larger n random
            let n = rng.gen_range_usize(100, 500);
            let m = rng.gen_range_usize(1, n);
            let k = rng.gen_range_usize(1, n);
            let s: Vec<i32> = (0..n).map(|_| if rng.next_u64() % 2 == 0 { 0 } else { 1 }).collect();
            (s, m, k)
        }
        _ => {
            let n = rng.gen_range_usize(1, 200);
            let m = rng.gen_range_usize(1, n);
            let k = rng.gen_range_usize(1, n);
            let s: Vec<i32> = (0..n).map(|_| if rng.next_u64() % 2 == 0 { 0 } else { 1 }).collect();
            (s, m, k)
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
        let mut cases: Vec<(Vec<i32>, usize, usize)> = Vec::new();
        let mut total = 0usize;
        for sub in 0..t {
            let mode = (count + sub) % modes;
            let (ss, sm, sk) = make_seed_case(&mut rng, mode);
            // Pass through verified function
            let case = generate_test_case(&ss, sm, sk);
            if total + case.0.len() > 10_000 { break; }
            total += case.0.len();
            cases.push(case);
        }
        if cases.is_empty() { continue; }
        let answers: Vec<i64> = cases.iter().map(|(s, m, k)| Solution::min_timar_operations(s.clone(), *m, *k)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
