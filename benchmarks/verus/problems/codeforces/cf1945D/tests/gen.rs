use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: usize, m_offset: usize, fillers_a: &Vec<i64>, fillers_b: &Vec<i64>) -> (result: (Vec<i64>, Vec<i64>, usize))
    requires
        1 <= seed_n <= 50,
        1 <= m_offset <= seed_n,
        fillers_a.len() == seed_n,
        fillers_b.len() == seed_n,
        forall |i: int| 0 <= i < fillers_a.len() ==> 1 <= #[trigger] fillers_a[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < fillers_b.len() ==> 1 <= #[trigger] fillers_b[i] <= 1_000_000_000,
    ensures
        1 <= result.2 <= result.0.len() <= 200_000,
        result.0.len() == result.1.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 1_000_000_000,
{
    let mut a: Vec<i64> = Vec::new();
    let mut b: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < seed_n
        invariant
            0 <= i <= seed_n,
            seed_n == fillers_a.len(),
            seed_n == fillers_b.len(),
            a.len() == i,
            b.len() == i,
            forall |j: int| 0 <= j < fillers_a.len() ==> 1 <= #[trigger] fillers_a[j] <= 1_000_000_000,
            forall |j: int| 0 <= j < fillers_b.len() ==> 1 <= #[trigger] fillers_b[j] <= 1_000_000_000,
            forall |j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
            forall |j: int| 0 <= j < b.len() ==> 1 <= #[trigger] b[j] <= 1_000_000_000,
        decreases seed_n - i,
    {
        a.push(fillers_a[i]);
        b.push(fillers_b[i]);
        i = i + 1;
    }
    (a, b, m_offset)
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

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1945);
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
            let n = rng.gen_range_usize(1, 20);
            let m = rng.gen_range_usize(1, n);
            let mut fa: Vec<i64> = Vec::with_capacity(n);
            let mut fb: Vec<i64> = Vec::with_capacity(n);
            for _ in 0..n {
                fa.push(rng.gen_range_i64(1, 100));
                fb.push(rng.gen_range_i64(1, 100));
            }
            let (a, b, mm) = generate_test_case(n, m, &fa, &fb);
            input.push_str(&format!("{} {}\n", a.len(), mm));
            let parts_a: Vec<String> = a.iter().map(|x| x.to_string()).collect();
            input.push_str(&parts_a.join(" "));
            input.push('\n');
            let parts_b: Vec<String> = b.iter().map(|x| x.to_string()).collect();
            input.push_str(&parts_b.join(" "));
            input.push('\n');
            let ans = Solution::min_coins(a, b, mm);
            output.push_str(&format!("{}\n", ans));
        }
        if !seen.insert(input.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&input), fmt_json_str(&output)).unwrap();
        count += 1;
    }
}
