use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    fill_val: i32,
    low_val: i32,
    high_val: i32,
    peak_pos: usize,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        3 <= n <= 1000,
        1 <= fill_val <= 1_000_000_000i32,
        1 <= low_val <= 999_999_999i32,
        low_val < high_val,
        high_val <= 1_000_000_000i32,
        1 <= peak_pos,
        peak_pos + 1 < n,
    ensures
        3 <= result.len() <= 1000,
        forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1_000_000_000i32,
        exists |a: int, b: int, c: int| 0 <= a < b < c < result.len() as int
            && result[a] < result[b] && result[b] > result[c],
{
    let mut nums: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            nums.len() == idx as int,
            3 <= n <= 1000,
            1 <= fill_val <= 1_000_000_000i32,
            forall|j: int| 0 <= j < idx as int ==> nums[j] == fill_val,
        decreases n - idx,
    {
        nums.push(fill_val);
        idx += 1;
    }

    let left: usize = peak_pos - 1;
    let right: usize = peak_pos + 1;

    nums.set(left, low_val);
    nums.set(peak_pos, high_val);
    nums.set(right, low_val);

    if mutation_kind == 1 && high_val < 1_000_000_000i32 {
        nums.set(peak_pos, (high_val + 1) as i32);
    } else if mutation_kind == 2 && low_val > 1 {
        nums.set(left, (low_val - 1) as i32);
        nums.set(right, (low_val - 1) as i32);
    } else if mutation_kind == 3 {
        nums.set(peak_pos, 1_000_000_000i32);
    } else if mutation_kind == 4 {
        nums.set(left, 1i32);
        nums.set(right, 1i32);
    } else if mutation_kind == 5 && low_val + 1 < high_val {
        nums.set(left, (low_val + 1) as i32);
    }

    assert(nums[left as int] < nums[peak_pos as int]);
    assert(nums[peak_pos as int] > nums[right as int]);
    assert(0 <= left as int && (left as int) < (peak_pos as int)
        && (peak_pos as int) < (right as int) && (right as int) < nums.len() as int
        && nums[left as int] < nums[peak_pos as int]
        && nums[peak_pos as int] > nums[right as int]);

    nums
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn build_nums(n: usize, fill_val: i32, low_val: i32, high_val: i32, peak_pos: usize, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(n, fill_val, low_val, high_val, peak_pos, mutation_kind)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1671);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::minimum_mountain_removals(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![1, 3, 1], &mut seen, &mut out, &mut count);
    emit(vec![2, 1, 1, 5, 6, 2, 3, 1], &mut seen, &mut out, &mut count);

    // Structured seeds: (n, fill_val, low_val, high_val, peak_pos)
    let seeds: Vec<(usize, i32, i32, i32, usize)> = vec![
        (3, 5, 1, 3, 1),
        (5, 100, 10, 200, 2),
        (10, 500, 100, 999_999_999, 5),
        (100, 42, 1, 1_000_000_000, 50),
        (1000, 1, 1, 2, 500),
        (1000, 999_999_999, 1, 1_000_000_000, 998),
        (3, 1, 1, 1_000_000_000, 1),
        (4, 500, 499, 501, 2),
        (50, 100, 50, 999, 1),
        (50, 100, 50, 999, 48),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    for &(n, fill_val, low_val, high_val, peak_pos) in &seeds {
        for &mk in &mutation_kinds {
            let nums = build_nums(n, fill_val, low_val, high_val, peak_pos, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    let mut _attempts_0 = 0usize;
    while count < target {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(3, 5),
            1 => rng.gen_range_usize(3, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };

        let fill_val = if rng.gen_range_usize(0, 4) == 0 {
            *[1i32, 1_000_000_000, 500_000_000].iter()
                .nth(rng.gen_range_usize(0, 2)).unwrap()
        } else {
            rng.gen_range_i64(1, 1_000_000_000) as i32
        };

        let low_val = rng.gen_range_i64(1, 999_999_999) as i32;
        let high_val = rng.gen_range_i64(low_val as i64 + 1, 1_000_000_000) as i32;
        let peak_pos = rng.gen_range_usize(1, n - 2);
        let mk = rng.gen_range_usize(0, 5) as u8;

        let nums = build_nums(n, fill_val, low_val, high_val, peak_pos, mk);
        emit(nums, &mut seen, &mut out, &mut count);
    }
}
