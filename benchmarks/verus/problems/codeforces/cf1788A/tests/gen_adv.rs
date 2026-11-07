use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, a: Vec<i32>) -> (res: (usize, Vec<i32>))
    requires
        2 <= n <= 1000,
        n == a.len(),
        forall|i: int| 0 <= i < n as int ==> #[trigger] a[i] == 1 || a[i] == 2,
    ensures
        2 <= res.0 <= 1000,
        res.0 == res.1.len(),
        forall|i: int| 0 <= i < res.0 as int ==> #[trigger] res.1[i] == 1 || res.1[i] == 2,
{
    (n, a)
}

pub fn build_vec(n: usize, pattern: &Vec<i32>) -> (res: Vec<i32>)
    requires
        2 <= n <= 1000,
        pattern.len() == n,
        forall|i: int| 0 <= i < n as int ==> #[trigger] pattern[i] == 1 || pattern[i] == 2,
    ensures
        res.len() == n,
        forall|i: int| 0 <= i < n as int ==> #[trigger] res[i] == 1 || res[i] == 2,
{
    let mut v: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            v.len() == i,
            pattern.len() == n,
            forall|k: int| 0 <= k < i as int ==> #[trigger] v[k] == 1 || v[k] == 2,
            forall|k: int| 0 <= k < n as int ==> #[trigger] pattern[k] == 1 || pattern[k] == 2,
        decreases n - i,
    {
        let x = pattern[i];
        v.push(x);
        i = i + 1;
    }
    v
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed.wrapping_add(1)) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % r) as i64) as i32
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

type TC = Vec<i32>;

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for a in cases {
        let ans = Solution::one_and_two(a.len(), a.clone());
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn gen_case(rng: &mut Rng, mode: usize) -> TC {
    match mode {
        0 => {
            // n=2
            (0..2).map(|_| rng.gen_range_i32(1, 2)).collect()
        }
        1 => {
            // all 1s
            let n = rng.gen_range_usize(2, 100);
            vec![1i32; n]
        }
        2 => {
            // all 2s, even count
            let n = 2 * rng.gen_range_usize(1, 50);
            vec![2i32; n]
        }
        3 => {
            // odd number of 2s -> -1
            let n = rng.gen_range_usize(2, 100);
            let mut v: Vec<i32> = (0..n).map(|_| if rng.next_u64() % 3 == 0 { 2i32 } else { 1i32 }).collect();
            // Count 2s, and if even, flip one element
            let twos = v.iter().filter(|&&x| x == 2).count();
            if twos % 2 == 0 {
                // flip one
                if let Some(i) = v.iter().position(|&x| x == 1) {
                    v[i] = 2;
                } else {
                    v[0] = 2;  // all 1s case, won't happen here
                }
            }
            v
        }
        4 => {
            // moderate-large random
            let n = rng.gen_range_usize(500, 1000);
            (0..n).map(|_| rng.gen_range_i32(1, 2)).collect()
        }
        _ => {
            let n = rng.gen_range_usize(2, 200);
            (0..n).map(|_| rng.gen_range_i32(1, 2)).collect()
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1788);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 100000 {
        tries += 1;
        let t: usize = if count % 5 == 0 { rng.gen_range_usize(2, 30) } else { 1 };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let mode = (rng.next_u64() as usize) % 6;
            cases.push(gen_case(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

