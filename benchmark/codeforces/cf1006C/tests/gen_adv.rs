use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, fillers: &Vec<i64>) -> (nums: Vec<i64>)
    requires
        1 <= n <= 200_000,
        fillers.len() == n,
        forall|i: int| 0 <= i < fillers.len() ==>
            1 <= (#[trigger] fillers[i]) as int && (fillers[i] as int) <= 1000,
    ensures
        1 <= nums.len() <= 200_000,
        nums.len() == n,
        forall|k: int| 0 <= k < nums.len() ==>
            1 <= (#[trigger] nums[k]) as int && (nums[k] as int) <= 1_000_000_000,
        forall|k: int| 0 <= k < nums.len() ==> nums[k] == fillers[k],
{
    let mut nums: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            1 <= n <= 200_000,
            0 <= i <= n,
            nums.len() == i,
            forall|j: int| 0 <= j < fillers.len() ==>
                1 <= (#[trigger] fillers[j]) as int && (fillers[j] as int) <= 1000,
            forall|k: int| 0 <= k < i as int ==> nums[k] == fillers[k],
            forall|k: int| 0 <= k < i as int ==>
                1 <= (#[trigger] nums[k]) as int && (nums[k] as int) <= 1_000_000_000,
        decreases n - i,
    {
        nums.push(fillers[i]);
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
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

fn build_input(nums: &[i64]) -> String {
    let mut s = format!("{}\n", nums.len());
    let parts: Vec<String> = nums.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i64) -> String { format!("{}\n", ans) }

fn random_array(rng: &mut Rng, len: usize, max_val: i64) -> Vec<i64> {
    (0..len).map(|_| rng.gen_range_i64(1, max_val)).collect()
}

fn make_pattern(rng: &mut Rng, n: usize, mode: usize) -> Vec<i64> {
    let mut v: Vec<i64> = Vec::with_capacity(n);
    match mode {
        0 => for _ in 0..n { v.push(1); },
        1 => for _ in 0..n { v.push(1_000_000_000); },
        2 => {
            for i in 0..n { v.push(if i % 2 == 0 { 1 } else { 1_000_000_000 }); }
        }
        3 => {
            for i in 0..n { v.push(((i as i64 * 17 + 1) % 1_000_000_000) + 1); }
        }
        4 => {
            for i in 0..n { if i == n/2 { v.push(1_000_000_000); } else { v.push(1); } }
        }
        5 => {
            for i in 0..n { if i == 0 || i + 1 == n { v.push(1_000_000_000); } else { v.push(1); } }
        }
        6 => {
            for i in 0..n {
                let k = if i < n - i - 1 { i } else { n - i - 1 };
                v.push(((k as i64 + 1) * 7) % 1_000_000_000 + 1);
            }
        }
        7 => {
            let half = n / 2;
            for i in 0..n {
                if i < half { v.push(1); }
                else if i == half && n % 2 == 1 { v.push(rng.gen_range_i64(1, 1_000)); }
                else { v.push(1); }
            }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range_i64(1, 1_000_000_000)); }
        }
    }
    v
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(987654321);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |nums: Vec<i64>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        // Hash-based dedup
        let mut h: u64 = 1469598103934665603;
        h ^= nums.len() as u64;
        h = h.wrapping_mul(1099511628211);
        for &x in &nums {
            h ^= x as u64;
            h = h.wrapping_mul(1099511628211);
        }
        if !seen.insert(h) { return; }
        let inp = build_input(&nums);
        let ans = Solution::max_equal_outer_sum(nums.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    emit(vec![1], &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000], &mut seen, &mut out, &mut count);

    for n in [2usize, 3, 4, 5, 7, 10, 100].iter() {
        emit(vec![1i64; *n], &mut seen, &mut out, &mut count);
        emit(vec![1_000_000_000i64; *n], &mut seen, &mut out, &mut count);
    }

    for n in [2usize, 3, 5, 10, 50, 100, 500, 1000, 5000, 10000, 30_000].iter() {
        for mode in 0..8 {
            if count >= target { break; }
            let v = make_pattern(&mut rng, *n, mode);
            emit(v, &mut seen, &mut out, &mut count);
        }
    }

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let n = match tries % 7 {
            0 => rng.gen_range_usize(1, 10),
            1 => rng.gen_range_usize(10, 100),
            2 => rng.gen_range_usize(100, 1000),
            3 => rng.gen_range_usize(1000, 10_000),
            4 => rng.gen_range_usize(10_000, 50_000),
            5 => rng.gen_range_usize(20_000, 50_000),
            _ => rng.gen_range_usize(50_000, 80_000),
        };
        let max_val = match tries % 5 {
            0 => 10i64,
            1 => 100,
            2 => 1_000,
            3 => 1_000_000,
            _ => 1_000_000_000,
        };
        let v = random_array(&mut rng, n, max_val);
        emit(v, &mut seen, &mut out, &mut count);
    }
}

