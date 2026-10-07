use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<u64>) -> (result: Vec<u64>)
    ensures
        1 <= result.len() <= 200000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000000000,
{
    let n = if values.len() < 1 { 1usize }
            else if values.len() > 200000 { 200000usize } else { values.len() };
    let limit = 1000000000;
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 200000,
            limit == 1000000000,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] <= limit,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 0 };
        let value = if value < 0 { 0 } else if value > limit { limit } else { value };
        result.push(value);
        i += 1;
    }
    result
}


pub fn generate_candidate(seed_n: usize, fillers: &Vec<u64>, mutation_kind: u8) -> (result: Vec<u64>)
    requires
        1 <= seed_n <= 50,
        fillers.len() == seed_n,
        forall |i: int| 0 <= i < fillers.len() ==> #[trigger] fillers[i] <= 1_000_000_000u64,
    ensures
        1 <= result.len() <= 200_000,
        forall |i: int| 0 <= i < result.len() ==> #[trigger] result[i] <= 1_000_000_000u64,
{
    let mut a: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < seed_n
        invariant
            seed_n == fillers.len(),
            1 <= seed_n <= 50,
            0 <= i <= seed_n,
            a.len() == i,
            forall |j: int| 0 <= j < fillers.len() ==> #[trigger] fillers[j] <= 1_000_000_000u64,
            forall |j: int| 0 <= j < a.len() ==> #[trigger] a[j] <= 1_000_000_000u64,
        decreases seed_n - i,
    {
        if mutation_kind == 0 {
            a.push(fillers[i]);
        } else if mutation_kind == 1 {
            a.push(0);
        } else if mutation_kind == 2 {
            a.push(1);
        } else if mutation_kind == 3 {
            // Construct a "good prefix" pattern: power-of-two sums
            a.push(if i == 0 { 0 } else { fillers[i] / 2 });
        } else if mutation_kind == 4 {
            a.push(1_000_000_000u64);
        } else {
            a.push(fillers[i] % 100);
        }
        i = i + 1;
    }
    a
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
        let range = (hi as u128 - lo as u128 + 1) as u128;
        (lo as u128 + (self.next_u64() as u128 % range)) as u64
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
    let mut rng = Rng::new(1985);
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
            let n = rng.gen_range_usize(1, 50);
            let mut fillers: Vec<u64> = Vec::with_capacity(n);
            for _ in 0..n {
                fillers.push(rng.gen_range_u64(0, 1_000_000_000u64));
            }
            let mk = (rng.next_u64() % 6) as u8;
            let a = generate_test_case(generate_candidate(n, &fillers, mk));
            input.push_str(&format!("{}\n", a.len()));
            let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
            input.push_str(&parts.join(" "));
            input.push('\n');
            let ans = Solution::count_good_prefixes_fn(a);
            output.push_str(&format!("{}\n", ans));
        }
        if !seen.insert(input.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&input), fmt_json_str(&output)).unwrap();
        count += 1;
    }
}
