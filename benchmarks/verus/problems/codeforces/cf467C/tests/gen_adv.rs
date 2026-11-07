use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    m: usize,
    k: usize,
    fillers: &Vec<i64>,
) -> (result: (Vec<i64>, usize, usize))
    requires
        1 <= n <= 5000,
        1 <= m,
        1 <= k,
        m * k <= n,
        m <= n,
        fillers.len() == n,
        forall |i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 1_000_000_000,
    ensures
        ({
            let (nums, mm, kk) = result;
            &&& 1 <= nums.len() <= 5000
            &&& 1 <= mm <= nums.len()
            &&& 1 <= kk
            &&& mm * kk <= nums.len()
            &&& (forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000)
        }),
{
    let mut nums: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            nums.len() == i,
            fillers.len() == n,
            forall |j: int| 0 <= j < i as int ==> 0 <= #[trigger] nums[j] <= 1_000_000_000,
            forall |j: int| 0 <= j < fillers.len() ==> 0 <= #[trigger] fillers[j] <= 1_000_000_000,
        decreases n - i,
    {
        nums.push(fillers[i]);
        i = i + 1;
    }
    (nums, m, k)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
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

fn random_array(rng: &mut Rng, len: usize) -> Vec<i64> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(0, 1_000_000_000));
    }
    arr
}

fn build_input(nums: &[i64], m: usize, k: usize) -> String {
    let n = nums.len();
    let mut s = format!("{} {} {}\n", n, m, k);
    let parts: Vec<String> = nums.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i128) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target_count: usize = 200;
    let mut rng = Rng::new(46703);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i64>, m: usize, k: usize, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if nums.is_empty() || m == 0 || k == 0 || m * k > nums.len() { return; }
        let key = format!("{:?}_{}_{}", nums, m, k);
        if !seen.insert(key) { return; }
        let result = Solution::max_k_segments_sum(nums.clone(), m, k);
        let inp = build_input(&nums, m, k);
        let outp = build_output(result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Adversarial: max n, with all max values
    let max_arr: Vec<i64> = vec![1_000_000_000; 5000];
    emit(max_arr.clone(), 1, 5000, &mut seen, &mut out, &mut count);
    emit(max_arr.clone(), 5000, 1, &mut seen, &mut out, &mut count);
    emit(max_arr.clone(), 50, 100, &mut seen, &mut out, &mut count);
    emit(max_arr.clone(), 100, 50, &mut seen, &mut out, &mut count);
    emit(max_arr.clone(), 25, 200, &mut seen, &mut out, &mut count);
    emit(max_arr.clone(), 71, 70, &mut seen, &mut out, &mut count);

    // All zeros
    let zero_arr: Vec<i64> = vec![0; 5000];
    emit(zero_arr.clone(), 1, 5000, &mut seen, &mut out, &mut count);
    emit(zero_arr.clone(), 50, 100, &mut seen, &mut out, &mut count);

    // Alternating min/max
    let alt: Vec<i64> = (0..5000).map(|i| if i % 2 == 0 { 0 } else { 1_000_000_000 }).collect();
    emit(alt.clone(), 1, 2500, &mut seen, &mut out, &mut count);
    emit(alt.clone(), 2, 100, &mut seen, &mut out, &mut count);
    emit(alt.clone(), 100, 5, &mut seen, &mut out, &mut count);

    // Stress: large arrays
    while count < target_count {
        let n = match count % 6 {
            0 => rng.gen_range_usize(2000, 5000),
            1 => rng.gen_range_usize(1000, 3000),
            2 => rng.gen_range_usize(500, 1500),
            3 => rng.gen_range_usize(100, 500),
            4 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(20, 100),
        };
        let arr = random_array(&mut rng, n);
        let m = rng.gen_range_usize(1, n);
        let max_k = n / m;
        let k = rng.gen_range_usize(1, max_k);
        emit(arr, m, k, &mut seen, &mut out, &mut count);
    }
}

