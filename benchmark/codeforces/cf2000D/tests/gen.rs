use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: usize, fillers_a: &Vec<i64>, fillers_s: &Vec<u8>) -> (result: (Vec<i64>, Vec<u8>))
    requires
        2 <= seed_n <= 30,
        fillers_a.len() == seed_n,
        fillers_s.len() == seed_n,
        forall |i: int| 0 <= i < fillers_a.len() ==> 1 <= #[trigger] fillers_a[i] <= 100_000,
        forall |i: int| 0 <= i < fillers_s.len() ==> #[trigger] fillers_s[i] == 1u8 || fillers_s[i] == 2u8,
    ensures
        2 <= result.0.len() <= 200_000,
        result.0.len() == result.1.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
        forall |i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i] == 1u8 || result.1[i] == 2u8,
{
    let mut a: Vec<i64> = Vec::new();
    let mut s: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < seed_n
        invariant
            0 <= i <= seed_n,
            seed_n == fillers_a.len(),
            seed_n == fillers_s.len(),
            a.len() == i,
            s.len() == i,
            forall |j: int| 0 <= j < fillers_a.len() ==> 1 <= #[trigger] fillers_a[j] <= 100_000,
            forall |j: int| 0 <= j < fillers_s.len() ==> #[trigger] fillers_s[j] == 1u8 || fillers_s[j] == 2u8,
            forall |j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 100_000,
            forall |j: int| 0 <= j < s.len() ==> #[trigger] s[j] == 1u8 || s[j] == 2u8,
        decreases seed_n - i,
    {
        a.push(fillers_a[i]);
        s.push(fillers_s[i]);
        i = i + 1;
    }
    (a, s)
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

fn vec_to_str(v: &Vec<u8>) -> String {
    let mut s = String::with_capacity(v.len());
    for x in v {
        s.push(if *x == 1 { 'L' } else { 'R' });
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(2000);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f_out = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f_out);
    let mut count = 0usize;
    let mut seen = HashSet::new();

    while count < target {
        let t = if count < 5 { 1usize } else { rng.gen_range_usize(1, 5) };
        let mut input = format!("{}\n", t);
        let mut output = String::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(2, 30);
            let mut fa: Vec<i64> = Vec::with_capacity(n);
            let mut fs: Vec<u8> = Vec::with_capacity(n);
            for _ in 0..n {
                fa.push(rng.gen_range_i64(1, 100));
                fs.push(if rng.next_u64() & 1 == 0 { 1u8 } else { 2u8 });
            }
            let (a, s) = generate_test_case(n, &fa, &fs);
            input.push_str(&format!("{}\n", a.len()));
            let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
            input.push_str(&parts.join(" "));
            input.push('\n');
            input.push_str(&format!("{}\n", vec_to_str(&s)));
            let ans = Solution::max_score(a, s);
            output.push_str(&format!("{}\n", ans));
        }
        if !seen.insert(input.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&input), fmt_json_str(&output)).unwrap();
        count += 1;
    }
}
