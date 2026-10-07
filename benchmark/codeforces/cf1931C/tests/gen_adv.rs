use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i64>) -> (result: Vec<i64>)
    ensures
        1 <= result.len() <= 200000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= result.len() as int,
{
    let n = if values.len() < 1 { 1usize }
            else if values.len() > 200000 { 200000usize } else { values.len() };
    let limit = n as i64;
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 200000,
            limit == n as i64,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= limit,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        let value = if value < 1 { 1 } else if value > limit { limit } else { value };
        result.push(value);
        i += 1;
    }
    result
}


pub fn generate_candidate(
    n: usize,
    fillers: &Vec<i64>,
) -> (a: Vec<i64>)
    requires
        1 <= n <= 200000,
        fillers.len() == n,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= n as i64,
    ensures
        1 <= a.len() <= 200000,
{
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 200000,
            fillers.len() == n,
            a.len() == i,
        decreases n - i,
    {
        a.push(fillers[i]);
        i = i + 1;
    }
    a
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

fn build_input_multi(cases: &[Vec<i64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output_multi(answers: &[i64]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn gen_mode(rng: &mut Rng, mode: usize) -> Vec<i64> {
    match mode {
        0 => {
            let n = rng.gen_range_usize(1, 200);
            let x = rng.gen_range_i64(1, n as i64);
            vec![x; n]
        }
        1 => {
            vec![1i64]
        }
        2 => {
            let n = rng.gen_range_usize(2, 200);
            let mut v = Vec::with_capacity(n);
            for i in 0..n { v.push(((i % n) + 1) as i64); }
            v
        }
        3 => {
            // left prefix equal, then different
            let n = rng.gen_range_usize(2, 200);
            let x = rng.gen_range_i64(1, n as i64);
            let mut y = rng.gen_range_i64(1, n as i64);
            if y == x { y = if x == 1 { 2 } else { x - 1 }; }
            let k = rng.gen_range_usize(1, n - 1);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i < k { v.push(x); } else { v.push(y); }
            }
            v
        }
        4 => {
            // right suffix equal
            let n = rng.gen_range_usize(2, 200);
            let x = rng.gen_range_i64(1, n as i64);
            let mut y = rng.gen_range_i64(1, n as i64);
            if y == x { y = if x == 1 { 2 } else { x - 1 }; }
            let k = rng.gen_range_usize(1, n - 1);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i >= k { v.push(x); } else { v.push(y); }
            }
            v
        }
        5 => {
            // prefix == suffix == x, middle different
            let n = rng.gen_range_usize(3, 200);
            let x = rng.gen_range_i64(1, n as i64);
            let mut y = rng.gen_range_i64(1, n as i64);
            if y == x { y = if x == 1 { 2 } else { x - 1 }; }
            let pref = rng.gen_range_usize(1, n / 2);
            let suff = rng.gen_range_usize(1, n / 2);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i < pref || i >= n - suff { v.push(x); } else { v.push(y); }
            }
            v
        }
        6 => {
            // larger n
            let n = rng.gen_range_usize(500, 2000);
            let mut v = Vec::with_capacity(n);
            for i in 0..n { v.push(((i % n) + 1) as i64); }
            v
        }
        7 => {
            // larger n all equal
            let n = rng.gen_range_usize(500, 2000);
            vec![1i64; n]
        }
        8 => {
            // ends equal but middle varies
            let n = rng.gen_range_usize(3, 500);
            let x = rng.gen_range_i64(1, n as i64);
            let mut v = Vec::with_capacity(n);
            v.push(x);
            for _ in 1..n-1 {
                v.push(rng.gen_range_i64(1, n as i64));
            }
            v.push(x);
            v
        }
        9 => {
            // ends different
            let n = rng.gen_range_usize(2, 500);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i64(1, n as i64));
            }
            v[0] = 1;
            v[n-1] = if (n as i64) > 1 { n as i64 } else { 1 };
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i64(1, n.max(1) as i64));
            }
            v
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
    let modes = 11usize;
    let _ = HashSet::<String>::new();

    while count < target {
        let t: usize = if count < 20 { 1 }
                       else if count < 80 { rng.gen_range_usize(2, 8) }
                       else if count < 150 { rng.gen_range_usize(3, 15) }
                       else { rng.gen_range_usize(5, 30) };

        let mut cases: Vec<Vec<i64>> = Vec::new();
        let mut total_n = 0usize;
        for sub in 0..t {
            let mode = (count * 7 + sub) % modes;
            let a = gen_mode(&mut rng, mode);
            if total_n + a.len() > 20_000 { break; }
            total_n += a.len();
            cases.push(a);
        }
        if cases.is_empty() { continue; }
        let answers: Vec<i64> = cases.iter().map(|a| Solution::min_cost_make_equal(a.clone())).collect();
        let cases: Vec<_> = cases.iter().cloned().map(generate_test_case).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
