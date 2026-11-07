use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i64>,
) -> (nums: Vec<i64>)
    requires
        1 <= fillers.len() <= 500_000,
        forall|i: int| 0 <= i < fillers.len() ==>
            -1_000_000_000 <= #[trigger] fillers[i] <= 1_000_000_000,
    ensures
        1 <= nums.len() <= 500_000,
        forall|k: int| 0 <= k < nums.len() ==>
            -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000,
{
    let n = fillers.len();
    let mut nums: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> nums[k] == fillers[k],
            forall|k: int| 0 <= k < fillers.len() ==>
                -1_000_000_000 <= #[trigger] fillers[k] <= 1_000_000_000,
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

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if nums.is_empty() || nums.len() > 500_000 { return; }
        for &v in &nums { if !(-1_000_000_000 <= v && v <= 1_000_000_000) { return; } }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let inp = build_input(&nums);
        let ans = Solution::count_equal_sum_splits(nums.clone());
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let mode = tries % 10;
        let n = match mode {
            0 => 1,
            1 => 100_000,
            2 => 50000,
            3 => rng.gen_range_usize(2, 20),
            4 => rng.gen_range_usize(50, 500),
            5 => rng.gen_range_usize(500, 5000),
            _ => rng.gen_range_usize(2, 1000),
        };
        let nums: Vec<i64> = match mode {
            0 => vec![rng.gen_range_i64(-1_000_000_000, 1_000_000_000)],
            1 => vec![0; n],
            2 => {
                // make all zeros so many splits
                vec![0i64; n]
            }
            3 => (0..n).map(|i| if i % 2 == 0 { 1 } else { -1 }).collect(),
            4 => (0..n).map(|_| rng.gen_range_i64(-100, 100)).collect(),
            5 => (0..n).map(|_| rng.gen_range_i64(-1_000_000_000, 1_000_000_000)).collect(),
            6 => {
                // Force prefixes equal target=1
                let mut v = vec![1i64];
                v.extend(vec![0; n / 3 - 1]);
                v.push(1);
                v.extend(vec![0; n / 3 - 1]);
                v.push(1);
                while v.len() < n { v.push(0); }
                v.truncate(n);
                v
            }
            _ => (0..n).map(|_| rng.gen_range_i64(-10, 10)).collect(),
        };
        emit(nums, &mut seen, &mut out, &mut count);
    }
}

