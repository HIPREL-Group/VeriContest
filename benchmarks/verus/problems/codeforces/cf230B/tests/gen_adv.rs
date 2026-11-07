use vstd::prelude::*;

verus! {

pub open spec fn is_prime_spec(n: int) -> bool {
    2 <= n && forall|d: int| 2 <= d && d <= n / d ==> #[trigger] (n % d) != 0
}

pub fn generate_test_case(x: u64) -> (res: u64)
    requires
        1 <= x <= 1_000_000_000_000u64,
    ensures
        1 <= res <= 1_000_000_000_000u64,
{
    x
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
    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        lo + (self.next_u64() % (hi - lo + 1))
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

fn build_input(nums: &[u64]) -> String {
    let mut s = format!("{}\n", nums.len());
    let parts: Vec<String> = nums.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "YES\n" } else { "NO\n" });
    }
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x230B);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Build small primes for T-prime generation
    let mut sieve = vec![true; 1_000_001];
    sieve[0] = false; sieve[1] = false;
    for i in 2..=1_000_000usize {
        if sieve[i] {
            let mut j = i*i;
            while j <= 1_000_000 {
                sieve[j] = false;
                j += i;
            }
        }
    }
    let primes: Vec<u64> = (2..=1_000_000usize).filter(|&i| sieve[i]).map(|i| i as u64).collect();

    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 10),
            1 => rng.gen_range_usize(10, 100),
            2 => rng.gen_range_usize(100, 1000),
            3 => rng.gen_range_usize(1000, 10000),
            _ => rng.gen_range_usize(10000, 100000),
        };
        let mut nums: Vec<u64> = Vec::with_capacity(n);
        for _ in 0..n {
            let kind = rng.next_u64() % 5;
            let v = match kind {
                0 => {
                    let p = primes[(rng.next_u64() as usize) % primes.len()];
                    p * p
                }
                1 => rng.gen_range_u64(1, 100),
                2 => rng.gen_range_u64(1, 1_000_000_000_000),
                3 => {
                    let r = rng.gen_range_u64(1, 1_000_000);
                    r * r
                }
                _ => rng.gen_range_u64(900_000_000_000, 1_000_000_000_000),
            };
            nums.push(v);
        }
        let inp = build_input(&nums);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::classify_t_primes(nums);
        let outp = build_output(&ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

