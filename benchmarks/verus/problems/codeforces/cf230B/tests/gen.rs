use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    vals: Vec<u64>,
    mutation_kind: u8,
) -> (result: Vec<u64>)
    requires
        1 <= n <= 100_000,
        vals.len() == n,
        forall|k: int| 0 <= k < vals.len() ==> 1u64 <= #[trigger] vals[k] <= 1_000_000_000_000u64,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 1u64 <= #[trigger] result[i] <= 1_000_000_000_000u64,
{
    if mutation_kind == 0 {
        // Identity: return vals as-is
        vals
    } else if mutation_kind == 1 && n >= 2 {
        // Shrink: drop last element
        let mut out: Vec<u64> = Vec::new();
        let mut i: usize = 0;
        while i < n - 1
            invariant
                0 <= i <= n - 1,
                out.len() == i,
                n >= 2,
                1 <= n <= 100_000,
                vals.len() == n,
                forall|k: int| 0 <= k < vals.len() ==> 1u64 <= #[trigger] vals[k] <= 1_000_000_000_000u64,
                forall|k: int| 0 <= k < out.len() ==> 1u64 <= #[trigger] out[k] <= 1_000_000_000_000u64,
            decreases n - 1 - i,
        {
            let v = vals[i];
            assert(1u64 <= vals[i as int] <= 1_000_000_000_000u64);
            out.push(v);
            i += 1;
        }
        out
    } else if mutation_kind == 2 && n < 100_000 {
        // Grow: push a 1
        let mut out: Vec<u64> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                out.len() == i,
                1 <= n <= 100_000,
                vals.len() == n,
                forall|k: int| 0 <= k < vals.len() ==> 1u64 <= #[trigger] vals[k] <= 1_000_000_000_000u64,
                forall|k: int| 0 <= k < out.len() ==> 1u64 <= #[trigger] out[k] <= 1_000_000_000_000u64,
            decreases n - i,
        {
            let v = vals[i];
            assert(1u64 <= vals[i as int] <= 1_000_000_000_000u64);
            out.push(v);
            i += 1;
        }
        out.push(1u64);
        assert(out[out.len() - 1] == 1u64);
        assert forall|k: int| 0 <= k < out.len() implies 1u64 <= #[trigger] out[k] <= 1_000_000_000_000u64 by {
            if k < n as int {
                assert(1u64 <= out[k] <= 1_000_000_000_000u64);
            } else {
                assert(k == out.len() - 1);
                assert(out[k] == 1u64);
            }
        }
        out
    } else if mutation_kind == 3 {
        // Set all elements to 1 (min boundary)
        let mut out: Vec<u64> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                out.len() == i,
                1 <= n <= 100_000,
                forall|k: int| 0 <= k < out.len() ==> #[trigger] out[k] == 1u64,
            decreases n - i,
        {
            out.push(1u64);
            i += 1;
        }
        assert forall|k: int| 0 <= k < out.len() implies 1u64 <= #[trigger] out[k] <= 1_000_000_000_000u64 by {
            assert(out[k] == 1u64);
        }
        out
    } else if mutation_kind == 4 {
        // Set all elements to 1_000_000_000_000 (max boundary)
        let mut out: Vec<u64> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                out.len() == i,
                1 <= n <= 100_000,
                forall|k: int| 0 <= k < out.len() ==> #[trigger] out[k] == 1_000_000_000_000u64,
            decreases n - i,
        {
            out.push(1_000_000_000_000u64);
            i += 1;
        }
        assert forall|k: int| 0 <= k < out.len() implies 1u64 <= #[trigger] out[k] <= 1_000_000_000_000u64 by {
            assert(out[k] == 1_000_000_000_000u64);
        }
        out
    } else if mutation_kind == 5 && n >= 2 {
        // Nudge first element up by 1 (if possible)
        let mut out: Vec<u64> = Vec::new();
        let v0 = if vals[0] < 1_000_000_000_000u64 { (vals[0] + 1) as u64 } else { vals[0] };
        out.push(v0);
        assert(1u64 <= v0 <= 1_000_000_000_000u64);
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                out.len() == i,
                1 <= n <= 100_000,
                n >= 2,
                vals.len() == n,
                forall|k: int| 0 <= k < vals.len() ==> 1u64 <= #[trigger] vals[k] <= 1_000_000_000_000u64,
                forall|k: int| 0 <= k < out.len() ==> 1u64 <= #[trigger] out[k] <= 1_000_000_000_000u64,
            decreases n - i,
        {
            let v = vals[i];
            assert(1u64 <= vals[i as int] <= 1_000_000_000_000u64);
            out.push(v);
            i += 1;
        }
        out
    } else {
        // Fallback: identity
        vals
    }
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

fn small_primes() -> Vec<u64> {
    let mut p = Vec::new();
    let limit = 1_000_000u64;
    let mut sieve = vec![true; limit as usize + 1];
    sieve[0] = false; sieve[1] = false;
    for i in 2..=(limit as usize) {
        if sieve[i] {
            p.push(i as u64);
            let mut j = i*i;
            while j <= limit as usize {
                sieve[j] = false;
                j += i;
            }
        }
    }
    p
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(230);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let primes = small_primes();

    // Examples
    let examples: Vec<Vec<u64>> = vec![
        vec![4, 5, 6],
        vec![1],
        vec![2],
        vec![1, 4, 9, 16, 25, 49],
        vec![1_000_000_000_000],
    ];
    for ex in &examples {
        if count >= target { break; }
        let inp = build_input(ex);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::classify_t_primes(ex.clone());
        let outp = build_output(&ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(500, 2000),
        };
        let mut nums: Vec<u64> = Vec::with_capacity(n);
        for _ in 0..n {
            let kind = rng.next_u64() % 4;
            let v = match kind {
                0 => {
                    // T-prime: square of small prime
                    let p = primes[(rng.next_u64() as usize) % primes.len()];
                    p * p
                }
                1 => {
                    // Small random
                    rng.gen_range_u64(1, 100)
                }
                2 => {
                    // Random in range
                    rng.gen_range_u64(1, 1_000_000_000_000)
                }
                _ => {
                    // Random square (might or might not be t-prime)
                    let r = rng.gen_range_u64(1, 1_000_000);
                    r * r
                }
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

