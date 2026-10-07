use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<u8>) -> (result: Vec<u8>)
    ensures
        1 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 3,
{
    let n = if values.len() < 1 { 1usize }
            else if values.len() > 50 { 50usize } else { values.len() };
    let limit = 3;
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 50,
            limit == 3,
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


pub open spec fn all_valid_digits(seq: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < seq.len() ==> 1 <= #[trigger] seq[i] as int <= 3
}

pub fn generate_candidate(digits: &Vec<u8>) -> (nums: Vec<u8>)
    requires
        1 <= digits.len() <= 100,
        forall|i: int| 0 <= i < digits.len() ==> 1 <= #[trigger] digits[i] as int <= 3,
    ensures
        1 <= nums.len() <= 100,
        nums.len() == digits.len(),
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] as int <= 3,
{
    let n = digits.len();
    let mut nums: Vec<u8> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            n == digits.len(),
            1 <= n <= 100,
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < digits.len() ==> 1 <= #[trigger] digits[k] as int <= 3,
            forall|k: int| 0 <= k < i as int ==> nums[k] == digits[k],
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] as int <= 3,
        decreases n - i,
    {
        let v = digits[i];
        nums.push(v);
        i = i + 1;
    }

    nums
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
    fn gen_digit(&mut self) -> u8 { self.gen_range_usize(1, 3) as u8 }
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

fn make_random(rng: &mut Rng, n: usize) -> Vec<u8> { (0..n).map(|_| rng.gen_digit()).collect() }
fn make_all_same(n: usize, d: u8) -> Vec<u8> { vec![d; n] }
fn make_sorted_asc(n: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    let third = n / 3;
    for _ in 0..third { v.push(1); }
    for _ in 0..third { v.push(2); }
    while v.len() < n { v.push(3); }
    v
}
fn make_sorted_desc(n: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    let third = n / 3;
    for _ in 0..third { v.push(3); }
    for _ in 0..third { v.push(2); }
    while v.len() < n { v.push(1); }
    v
}
fn make_alternating(n: usize) -> Vec<u8> { (0..n).map(|i| ((i % 3) + 1) as u8).collect() }
fn make_alt_two(n: usize, a: u8, b: u8) -> Vec<u8> { (0..n).map(|i| if i % 2 == 0 { a } else { b }).collect() }
fn make_only_two_values(rng: &mut Rng, n: usize, a: u8, b: u8) -> Vec<u8> {
    (0..n).map(|_| if rng.next_u64() % 2 == 0 { a } else { b }).collect()
}

fn build_input(nums: &[u8]) -> String {
    let parts: Vec<String> = nums.iter().map(|x| x.to_string()).collect();
    let mut s = parts.join("+");
    s.push('\n');
    s
}
fn build_output(sorted: &[u8]) -> String {
    let parts: Vec<String> = sorted.iter().map(|x| x.to_string()).collect();
    let mut s = parts.join("+");
    s.push('\n');
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let mut t = 0usize;
    while count < target {
        let mode = t % 11;
        t += 1;
        let mut digits: Vec<u8> = match mode {
            0 => vec![1],
            1 => vec![2],
            2 => vec![3],
            3 => { let n = rng.gen_range_usize(1, 100); make_random(&mut rng, n) }
            4 => { let n = rng.gen_range_usize(1, 100); make_all_same(n, 1) }
            5 => { let n = rng.gen_range_usize(1, 100); make_all_same(n, 3) }
            6 => make_sorted_asc(100),
            7 => make_sorted_desc(100),
            8 => { let n = rng.gen_range_usize(2, 100); make_alternating(n) }
            9 => { let n = rng.gen_range_usize(2, 100); make_alt_two(n, 1, 3) }
            _ => { let n = rng.gen_range_usize(1, 100); make_only_two_values(&mut rng, n, 1, 3) }
        };
        if digits.is_empty() { digits.push(1); }
        if digits.len() > 100 { digits.truncate(100); }
        for x in digits.iter_mut() { if *x < 1 || *x > 3 { *x = 1; } }
        let key = format!("{:?}", digits);
        if !seen.insert(key) { continue; }
        let digits = generate_test_case(digits);
        let inp = build_input(&digits);
        let sorted = Solution::sort_digits(digits.clone());
        let outs = build_output(&sorted);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
        if t > 100000 { break; }
    }
}
