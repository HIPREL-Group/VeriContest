use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 100_000,
        forall|k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 100_000,
    ensures
        1 <= nums.len() <= 100_000,
        forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100_000,
{
    let n = vals.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            1 <= n <= 100_000,
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 100_000,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100_000,
            forall|k: int| 0 <= k < i as int ==> nums[k] == vals[k],
        decreases n - i,
    {
        nums.push(vals[i]);
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

fn build_input(nums: &[i32]) -> String {
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

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if nums.is_empty() || nums.len() > 100_000 { return; }
        for &v in &nums { if !(1 <= v && v <= 100_000) { return; } }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let inp = build_input(&nums);
        let ans = Solution::max_boredom_points(nums.clone());
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
            _ => rng.gen_range_usize(1, 1000),
        };
        let nums: Vec<i32> = match mode {
            0 => vec![rng.gen_range_i32(1, 100_000)],
            1 => vec![1; n],
            2 => vec![100_000; n],
            3 => (0..n).map(|i| (i as i32 % 10 + 1)).collect(),
            4 => (0..n).map(|_| rng.gen_range_i32(1, 100)).collect(),
            5 => (0..n).map(|_| rng.gen_range_i32(1, 100_000)).collect(),
            6 => (0..n).map(|i| if i % 2 == 0 { 1 } else { 2 }).collect(),
            7 => {
                let mut v = Vec::with_capacity(n);
                for i in 0..n { v.push((i as i32) % 5 + 1); } v
            }
            _ => (0..n).map(|_| rng.gen_range_i32(1, 10)).collect(),
        };
        emit(nums, &mut seen, &mut out, &mut count);
    }
}

