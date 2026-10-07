use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a: Vec<i64>,
    queries: Vec<(usize, usize)>,
) -> (res: (Vec<i64>, Vec<(usize, usize)>))
    requires
        2 <= a.len() <= 200000,
        forall|i: int| 0 <= i < a.len() as int ==> 1 <= #[trigger] a[i] <= 1000000,
        forall|k: int| 0 <= k < queries.len() as int ==> 1 <= #[trigger] queries[k].0 < queries[k].1 <= a.len(),
    ensures
        2 <= res.0.len() <= 200000,
        forall|i: int| 0 <= i < res.0.len() as int ==> 1 <= #[trigger] res.0[i] <= 1000000,
        forall|k: int| 0 <= k < res.1.len() as int ==> 1 <= #[trigger] res.1[k].0 < res.1[k].1 <= res.0.len(),
{
    (a, queries)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed.wrapping_add(0x9E3779B97F4A7C15)) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
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

fn build_a(rng: &mut Rng, mode: usize, n: usize) -> Vec<i64> {
    let mut a: Vec<i64> = Vec::with_capacity(n);
    match mode {
        0 => {
            let v = rng.gen_range_i64(1, 1_000_000);
            for _ in 0..n { a.push(v); }
        }
        1 => {
            let v1 = rng.gen_range_i64(1, 500_000);
            let v2 = rng.gen_range_i64(500_001, 1_000_000);
            for i in 0..n { a.push(if i % 2 == 0 { v1 } else { v2 }); }
        }
        2 => {
            let v = rng.gen_range_i64(1, 999_999);
            for _ in 0..(n - 1) { a.push(v); }
            a.push(v + 1);
        }
        3 => {
            let v = rng.gen_range_i64(2, 1_000_000);
            a.push(v - 1);
            for _ in 1..n { a.push(v); }
        }
        4 => {
            let v = rng.gen_range_i64(1, 999_999);
            for _ in 0..n { a.push(v); }
            a[n / 2] = v + 1;
        }
        5 => {
            let block = 1 + (rng.gen_range_usize(0, 20));
            let mut cur: i64 = rng.gen_range_i64(1, 1_000_000);
            for i in 0..n {
                if i > 0 && i % block == 0 {
                    cur = rng.gen_range_i64(1, 1_000_000);
                }
                a.push(cur);
            }
        }
        6 => {
            for _ in 0..n { a.push(rng.gen_range_i64(1, 3)); }
        }
        7 => {
            for _ in 0..n { a.push(rng.gen_range_i64(1, 1_000_000)); }
        }
        8 => {
            let v1 = rng.gen_range_i64(1, 500_000);
            let v2 = rng.gen_range_i64(500_001, 1_000_000);
            let mid = n / 2;
            for i in 0..n { a.push(if i < mid { v1 } else { v2 }); }
        }
        9 => {
            for i in 0..n { a.push(1 + (i as i64 % 1_000_000)); }
        }
        _ => {
            for _ in 0..n { a.push(rng.gen_range_i64(1, 10)); }
        }
    }
    a
}

fn build_queries(rng: &mut Rng, n: usize, q: usize) -> Vec<(usize, usize)> {
    let mut qs: Vec<(usize, usize)> = Vec::with_capacity(q);
    for k in 0..q {
        let choice = k % 5;
        let (l, r) = match choice {
            0 => (1usize, n),
            1 => {
                let l = rng.gen_range_usize(1, n - 1);
                (l, l + 1)
            }
            2 => {
                let l = rng.gen_range_usize(1, n - 1);
                (l, n)
            }
            3 => {
                let r = rng.gen_range_usize(2, n);
                (1usize, r)
            }
            _ => {
                let l = rng.gen_range_usize(1, n - 1);
                let r = rng.gen_range_usize(l + 1, n);
                (l, r)
            }
        };
        qs.push((l, r));
    }
    qs
}

fn build_case(a: &[i64], queries: &[(usize, usize)]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s.push_str(&format!("{}\n", queries.len()));
    for &(l, r) in queries {
        s.push_str(&format!("{} {}\n", l, r));
    }
    s
}

fn build_input_multi(cases: &[(Vec<i64>, Vec<(usize, usize)>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, q) in cases {
        s.push_str(&build_case(a, q));
    }
    s
}

fn build_output_multi(answers: &[Vec<(i32, i32)>]) -> String {
    let mut s = String::new();
    for (i, ans) in answers.iter().enumerate() {
        for &(x, y) in ans {
            s.push_str(&format!("{} {}\n", x, y));
        }
        if i + 1 < answers.len() {
            s.push('\n');
        }
    }
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;
    let modes = 11usize;

    while count < target {
        let t: usize = if count < 10 { 1 }
                       else if count < 60 { rng.gen_range_usize(2, 8) }
                       else if count < 120 { rng.gen_range_usize(3, 15) }
                       else { rng.gen_range_usize(5, 30) };

        let mut cases: Vec<(Vec<i64>, Vec<(usize, usize)>)> = Vec::new();
        let mut answers: Vec<Vec<(i32, i32)>> = Vec::new();
        let mut total_n = 0usize;
        let mut total_q = 0usize;

        for sub in 0..t {
            // adversarial: large n & q occasionally
            let n = match (count + sub) % 9 {
                0 => 2,
                1 => 3,
                2 => 10,
                3 => rng.gen_range_usize(80, 300),
                4 => rng.gen_range_usize(300, 1000),
                5 => rng.gen_range_usize(50, 200),
                6 => rng.gen_range_usize(500, 2000),
                7 => 5,
                _ => rng.gen_range_usize(20, 100),
            };
            let mode = (count * 7 + sub) % modes;
            let a = build_a(&mut rng, mode, n);
            let max_q = 30.min(n);
            let q = match (count + sub) % 5 {
                0 => 1,
                1 => 5.min(max_q),
                2 => 15.min(max_q),
                _ => max_q,
            };
            // bound the total to keep file modest
            if total_n + n > 50_000 || total_q + q > 50_000 { break; }
            let queries = build_queries(&mut rng, n, q);

            let key = format!("{:?}|{:?}", a, queries);
            if !seen.insert(key) { continue; }

            let ans = Solution::find_different_ones(a.clone(), queries.clone());
            total_n += n;
            total_q += q;
            cases.push((a, queries));
            answers.push(ans);
        }

        if cases.is_empty() { continue; }
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

