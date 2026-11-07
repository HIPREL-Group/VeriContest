use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_owners: &Vec<i64>,
    seed_k: i64,
) -> (res: (Vec<i64>, i64))
    requires
        2 <= seed_owners.len() <= 200000,
        1 <= seed_k <= 1000000000,
        forall|i: int| 0 <= i < seed_owners.len() ==>
            (#[trigger] seed_owners[i] == 0 || seed_owners[i] == 1),
    ensures
        2 <= res.0.len() <= 200000,
        1 <= res.1 <= 1000000000,
        forall|i: int| 0 <= i < res.0.len() ==>
            (#[trigger] res.0[i] == 0 || res.0[i] == 1),
{
    let n = seed_owners.len();
    let mut owners: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == seed_owners.len(),
            2 <= n <= 200000,
            0 <= i <= n,
            owners.len() == i,
            forall|j: int| 0 <= j < seed_owners.len() ==>
                (#[trigger] seed_owners[j] == 0 || seed_owners[j] == 1),
            forall|j: int| 0 <= j < i as int ==>
                (#[trigger] owners[j] == 0 || owners[j] == 1),
        decreases n - i,
    {
        owners.push(seed_owners[i]);
        i = i + 1;
    }
    (owners, seed_k)
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

fn build_input(cases: &[(Vec<i64>, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (owners, k) in cases {
        let n = owners.len();
        s.push_str(&format!("{} {}\n", n, k));
        let mut row = String::with_capacity(n);
        for &v in owners {
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

fn make_seed_case(rng: &mut Rng, mode: usize) -> (Vec<i64>, i64) {
    match mode {
        0 => {
            // all zeros
            let n = rng.gen_range_usize(2, 100);
            let k = rng.gen_range_i64(1, 100);
            (vec![0; n], k)
        }
        1 => {
            // all ones
            let n = rng.gen_range_usize(2, 100);
            let k = rng.gen_range_i64(1, 1000);
            (vec![1; n], k)
        }
        2 => {
            // alternating 01
            let n = rng.gen_range_usize(2, 100);
            let k = rng.gen_range_i64(1, 1000);
            ((0..n).map(|i| if i % 2 == 0 { 0 } else { 1 }).collect(), k)
        }
        3 => {
            // first half 0, second half 1
            let n = rng.gen_range_usize(4, 100);
            let mid = n / 2;
            let k = rng.gen_range_i64(1, n as i64);
            ((0..n).map(|i| if i < mid { 0 } else { 1 }).collect(), k)
        }
        4 => {
            // larger n
            let n = rng.gen_range_usize(100, 500);
            let k = rng.gen_range_i64(1, 1_000_000);
            ((0..n).map(|_| rng.gen_range_i64(0, 1)).collect(), k)
        }
        5 => {
            // first half 1, second half 0
            let n = rng.gen_range_usize(4, 100);
            let mid = n / 2;
            let k = rng.gen_range_i64(1, n as i64);
            ((0..n).map(|i| if i < mid { 1 } else { 0 }).collect(), k)
        }
        _ => {
            let n = rng.gen_range_usize(2, 200);
            let k = rng.gen_range_i64(1, (n*n) as i64);
            ((0..n).map(|_| rng.gen_range_i64(0, 1)).collect(), k)
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
        let mut cases: Vec<(Vec<i64>, i64)> = Vec::new();
        let mut total = 0usize;
        for sub in 0..t {
            let mode = (count + sub) % modes;
            let (so, sk) = make_seed_case(&mut rng, mode);
            // Pass through verified function
            let case = generate_test_case(&so, sk);
            if total + case.0.len() > 10_000 { break; }
            total += case.0.len();
            cases.push(case);
        }
        if cases.is_empty() { continue; }
        let answers: Vec<i64> = cases.iter().map(|(o, k)| Solution::minimum_groups(o.clone(), *k)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
