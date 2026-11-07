use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_n: i32,
    seed_d: i32,
    seed_left: &Vec<i32>,
    seed_right: &Vec<i32>,
) -> (res: (i32, i32, Vec<i32>, Vec<i32>))
    requires
        1 <= seed_n <= 100000,
        1 <= seed_d <= seed_n,
        1 <= seed_left.len() <= seed_n as nat,
        seed_left.len() == seed_right.len(),
        forall|j: int| 0 <= j < seed_left.len() as int ==>
            1 <= (#[trigger] seed_left[j]) <= seed_right[j] <= seed_n,
    ensures
        1 <= res.0 <= 100000,
        1 <= res.1 <= res.0,
        1 <= res.2.len() <= res.0 as nat,
        res.2.len() == res.3.len(),
        forall|j: int| 0 <= j < res.2.len() as int ==>
            1 <= (#[trigger] res.2[j]) <= res.3[j] <= res.0,
{
    let n = seed_left.len();
    let mut left: Vec<i32> = Vec::new();
    let mut right: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == seed_left.len(),
            n == seed_right.len(),
            1 <= n <= seed_n as nat,
            0 <= i <= n,
            left.len() == i,
            right.len() == i,
            1 <= seed_n <= 100000,
            1 <= seed_d <= seed_n,
            forall|j: int| 0 <= j < seed_left.len() as int ==>
                1 <= (#[trigger] seed_left[j]) <= seed_right[j] <= seed_n,
            forall|j: int| 0 <= j < i as int ==>
                1 <= (#[trigger] left[j]) <= right[j] <= seed_n,
        decreases n - i,
    {
        left.push(seed_left[i]);
        right.push(seed_right[i]);
        i = i + 1;
    }
    (seed_n, seed_d, left, right)
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

fn build_input(cases: &[(i32, i32, Vec<i32>, Vec<i32>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, d, left, right) in cases {
        let k = left.len();
        s.push_str(&format!("{} {} {}\n", n, d, k));
        for i in 0..k {
            s.push_str(&format!("{} {}\n", left[i], right[i]));
        }
    }
    s
}

fn build_output(answers: &[(i32, i32)]) -> String {
    let mut s = String::new();
    for &(b, m) in answers {
        s.push_str(&format!("{} {}\n", b, m));
    }
    s
}

fn make_seed_case(rng: &mut Rng, mode: usize) -> (i32, i32, Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // n=1
            (1i32, 1i32, vec![1], vec![1])
        }
        1 => {
            // d = n (only one start)
            let n = rng.gen_range_i64(1, 100) as i32;
            let k = rng.gen_range_usize(1, n as usize);
            let mut left = Vec::with_capacity(k);
            let mut right = Vec::with_capacity(k);
            for _ in 0..k {
                let l = rng.gen_range_i64(1, n as i64) as i32;
                let r = rng.gen_range_i64(l as i64, n as i64) as i32;
                left.push(l);
                right.push(r);
            }
            (n, n, left, right)
        }
        2 => {
            // d=1
            let n = rng.gen_range_i64(1, 100) as i32;
            let k = rng.gen_range_usize(1, n as usize);
            let mut left = Vec::with_capacity(k);
            let mut right = Vec::with_capacity(k);
            for _ in 0..k {
                let l = rng.gen_range_i64(1, n as i64) as i32;
                let r = rng.gen_range_i64(l as i64, n as i64) as i32;
                left.push(l);
                right.push(r);
            }
            (n, 1, left, right)
        }
        3 => {
            // larger n
            let n = rng.gen_range_i64(100, 500) as i32;
            let d = rng.gen_range_i64(1, n as i64) as i32;
            let k = rng.gen_range_usize(1, (n as usize).min(50));
            let mut left = Vec::with_capacity(k);
            let mut right = Vec::with_capacity(k);
            for _ in 0..k {
                let l = rng.gen_range_i64(1, n as i64) as i32;
                let r = rng.gen_range_i64(l as i64, n as i64) as i32;
                left.push(l);
                right.push(r);
            }
            (n, d, left, right)
        }
        4 => {
            // all same job
            let n = rng.gen_range_i64(5, 50) as i32;
            let d = rng.gen_range_i64(1, n as i64) as i32;
            let k = rng.gen_range_usize(1, n as usize);
            let l = rng.gen_range_i64(1, n as i64) as i32;
            let r = rng.gen_range_i64(l as i64, n as i64) as i32;
            (n, d, vec![l; k], vec![r; k])
        }
        5 => {
            // jobs covering whole range
            let n = rng.gen_range_i64(5, 50) as i32;
            let d = rng.gen_range_i64(1, n as i64) as i32;
            let k = rng.gen_range_usize(1, n as usize);
            let left: Vec<i32> = vec![1; k];
            let right: Vec<i32> = vec![n; k];
            (n, d, left, right)
        }
        _ => {
            let n = rng.gen_range_i64(1, 100) as i32;
            let d = rng.gen_range_i64(1, n as i64) as i32;
            let k = rng.gen_range_usize(1, n as usize);
            let mut left = Vec::with_capacity(k);
            let mut right = Vec::with_capacity(k);
            for _ in 0..k {
                let l = rng.gen_range_i64(1, n as i64) as i32;
                let r = rng.gen_range_i64(l as i64, n as i64) as i32;
                left.push(l);
                right.push(r);
            }
            (n, d, left, right)
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
        let mut cases: Vec<(i32, i32, Vec<i32>, Vec<i32>)> = Vec::new();
        let mut total = 0usize;
        for sub in 0..t {
            let mode = (count + sub) % modes;
            let (sn, sd, sl, sr) = make_seed_case(&mut rng, mode);
            // pass through verified function
            let case = generate_test_case(sn, sd, &sl, &sr);
            let sz = case.0 as usize + case.2.len();
            if total + sz > 10_000 { break; }
            total += sz;
            cases.push(case);
        }
        if cases.is_empty() { continue; }
        let answers: Vec<(i32, i32)> = cases.iter().map(|(n, d, l, r)| Solution::best_start_days(*n, *d, l.clone(), r.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
