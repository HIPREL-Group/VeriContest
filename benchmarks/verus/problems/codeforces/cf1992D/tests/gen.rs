use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: usize, m: usize, k: i64, fillers: &Vec<u8>) -> (result: (Vec<u8>, usize, i64))
    requires
        1 <= seed_n <= 50,
        1 <= m <= 10,
        0 <= k <= 200_000,
        fillers.len() == seed_n,
        forall |i: int| 0 <= i < fillers.len() ==> #[trigger] fillers[i] <= 2u8,
    ensures
        1 <= result.0.len() <= 200_000,
        1 <= result.1 <= 10,
        0 <= result.2 <= 200_000,
        forall |i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i] <= 2u8,
{
    let mut a: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < seed_n
        invariant
            0 <= i <= seed_n,
            seed_n == fillers.len(),
            a.len() == i,
            forall |j: int| 0 <= j < fillers.len() ==> #[trigger] fillers[j] <= 2u8,
            forall |j: int| 0 <= j < a.len() ==> #[trigger] a[j] <= 2u8,
        decreases seed_n - i,
    {
        a.push(fillers[i]);
        i = i + 1;
    }
    (a, m, k)
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
        s.push(match x {
            0 => 'W',
            1 => 'C',
            2 => 'L',
            _ => 'W',
        });
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1992);
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
            let n = rng.gen_range_usize(1, 30);
            let m = rng.gen_range_usize(1, 10);
            let k = rng.gen_range_i64(0, 30);
            let mut fa: Vec<u8> = Vec::with_capacity(n);
            for _ in 0..n {
                fa.push(((rng.next_u64() % 3) as u8));
            }
            let (a, mm, kk) = generate_test_case(n, m, k, &fa);
            input.push_str(&format!("{} {} {}\n", a.len(), mm, kk));
            input.push_str(&format!("{}\n", vec_to_str(&a)));
            let ans = Solution::can_cross(a, mm, kk);
            output.push_str(if ans { "YES\n" } else { "NO\n" });
        }
        if !seen.insert(input.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&input), fmt_json_str(&output)).unwrap();
        count += 1;
    }
}
