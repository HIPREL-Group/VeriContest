use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    start: i64,
    diff: i64,
) -> (nums: Vec<i64>)
    requires
        1 <= n <= 100_000,
        1 <= start <= 50_000_000,
        0 <= diff <= 500,
        start + (n as i64) * diff <= 100_000_000,
    ensures
        1 <= nums.len() <= 100_000,
        nums.len() == n,
        forall|i: int| 0 <= i < nums.len() - 1 ==> #[trigger] nums[i] <= nums[i + 1],
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000_000,
{
    let mut nums: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            nums.len() == i,
            1 <= n <= 100_000,
            1 <= start <= 50_000_000,
            0 <= diff <= 500,
            start + (n as i64) * diff <= 100_000_000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == start + k * diff,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100_000_000,
        decreases n - i,
    {
        assert(0 <= (i as int) < n as int);
        assert((i as int) * (diff as int) <= (n as int) * (diff as int)) by {
            vstd::arithmetic::mul::lemma_mul_inequality(i as int, n as int, diff as int);
        };
        let val: i64 = start + (i as i64) * diff;
        assert(val as int == start as int + (i as int) * (diff as int));
        assert(1 <= val <= 100_000_000);
        nums.push(val);
        
        proof {
            assert forall|k: int| 0 <= k < (i + 1) as int implies #[trigger] nums[k] == start + k * diff by {
                if k < i as int {
                    assert(nums[k] == start + k * diff);
                } else {
                    assert(k == i as int);
                    assert(nums[k] == val);
                }
            }
        }
        i = i + 1;
    }

    proof {
        assert forall|j: int| 0 <= j < nums.len() - 1 implies #[trigger] nums[j] <= nums[j + 1] by {
            assert(nums[j] == start + j * diff);
            assert(nums[j + 1] == start + (j + 1) * diff);
            assert((j + 1) * diff == j * diff + diff) by {
                vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(diff as int, j, 1);
            };
        }
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

fn build_output(opt: Option<Vec<i64>>) -> String {
    match opt {
        None => "-1\n".to_string(),
        Some(ans) => {
            let mut s = format!("{}\n", ans.len());
            if !ans.is_empty() {
                let parts: Vec<String> = ans.iter().map(|x| x.to_string()).collect();
                s.push_str(&parts.join(" "));
                s.push('\n');
            }
            s
        }
    }
}

fn pick_params(rng: &mut Rng, mode: usize) -> (usize, i64, i64) {
    match mode {
        0 => (1, rng.gen_range_i64(1, 50_000_000), rng.gen_range_i64(0, 500)),
        1 => (2, rng.gen_range_i64(1, 50_000_000), rng.gen_range_i64(0, 500)),
        2 => (rng.gen_range_usize(2, 100), rng.gen_range_i64(1, 50_000_000), 0),
        3 => (rng.gen_range_usize(2, 10), rng.gen_range_i64(1, 20), rng.gen_range_i64(1, 10)),
        4 => (100_000, rng.gen_range_i64(1, 100), rng.gen_range_i64(0, 500)),
        5 => (rng.gen_range_usize(3, 1000), rng.gen_range_i64(1, 1000), 1),
        6 => (rng.gen_range_usize(2, 100), 1, rng.gen_range_i64(0, 500)),
        7 => {
            let diff = rng.gen_range_i64(1, 500);
            let n = rng.gen_range_usize(10, 100) as i64;
            let max_start = 100_000_000 - n * diff;
            let max_start_clamped = if max_start > 50_000_000 { 50_000_000 } else { max_start };
            let ms = if max_start_clamped < 1 { 1 } else { max_start_clamped };
            (n as usize, rng.gen_range_i64(1, ms), diff)
        }
        8 => (3, rng.gen_range_i64(1, 1_000_000), rng.gen_range_i64(0, 500)),
        9 => (rng.gen_range_usize(2, 50), rng.gen_range_i64(1, 1000), 500),
        _ => (rng.gen_range_usize(1, 500), rng.gen_range_i64(1, 1_000_000), rng.gen_range_i64(0, 100)),
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let modes = 11usize;
    let mut t = 0usize;

    while count < target {
        let mode = t % modes;
        t += 1;
        let (n, start, diff) = pick_params(&mut rng, mode);
        if n < 1 || n > 100_000 { continue; }
        if start < 1 || start > 50_000_000 { continue; }
        if diff < 0 || diff > 500 { continue; }
        let max_val = start + (n as i64) * diff;
        if max_val > 100_000_000 { continue; }
        let nums: Vec<i64> = (0..n).map(|i| start + (i as i64) * diff).collect();
        let key = format!("{} {} {} {}", n, start, diff, t % 3);
        if !seen.insert(key) { continue; }
        let inp = build_input(&nums);
        let mut sorted = nums.clone();
        sorted.sort_unstable();
        let ans = Solution::arithmetic_progression_insertions(sorted);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
        if t > 100000 { break; }
    }
}

