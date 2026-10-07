use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> -100000 <= #[trigger] nums[i] <= 100000,
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> -100000 <= #[trigger] result[i] <= 100000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set all elements to the same value (constant array — both monotone inc and dec)
        let val = nums[0];
        let mut r = nums;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == nums.len(),
                1 <= r.len() <= 100000,
                -100000 <= val <= 100000,
                forall|j: int| 0 <= j < i ==> r[j] == val,
                forall|j: int| i <= j < r.len() ==> -100000 <= #[trigger] r[j] <= 100000,
            decreases r.len() - i,
        {
            r.set(i, val);
            i += 1;
        }
        r
    } else if mutation_kind == 2 && nums.len() < 100000 {
        // grow by one element (push last element again)
        let mut r = nums;
        let last_val = r[r.len() - 1];
        r.push(last_val);
        r
    } else if mutation_kind == 3 && nums.len() > 1 {
        // shrink by one element (pop last)
        let mut r = nums;
        r.pop();
        r
    } else if mutation_kind == 4 {
        // nudge first element up (if < 100000)
        let mut r = nums;
        if r[0] < 100000 {
            r.set(0, r[0] + 1);
        }
        r
    } else if mutation_kind == 5 {
        // nudge first element down (if > -100000)
        let mut r = nums;
        if r[0] > -100000 {
            r.set(0, r[0] - 1);
        }
        r
    } else if mutation_kind == 6 {
        // nudge last element up (if < 100000)
        let mut r = nums;
        let last = r.len() - 1;
        if r[last] < 100000 {
            r.set(last, r[last] + 1);
        }
        r
    } else if mutation_kind == 7 {
        // nudge last element down (if > -100000)
        let mut r = nums;
        let last = r.len() - 1;
        if r[last] > -100000 {
            r.set(last, r[last] - 1);
        }
        r
    } else if mutation_kind == 8 {
        // set first element to 0
        let mut r = nums;
        r.set(0, 0);
        r
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // swap first two elements
        let mut r = nums;
        let a = r[0];
        let b = r[1];
        r.set(0, b);
        r.set(1, a);
        r
    } else if mutation_kind == 10 {
        // set last element to boundary -100000
        let mut r = nums;
        let last = r.len() - 1;
        r.set(last, -100000);
        r
    } else if mutation_kind == 11 {
        // set last element to boundary 100000
        let mut r = nums;
        let last = r.len() - 1;
        r.set(last, 100000);
        r
    } else {
        // fallback: identity
        nums
    }
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
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

/// Build a monotone increasing array of given length with values in [-100000, 100000].
fn build_increasing(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    let mut cur = rng.gen_range_i64(-100000, 100000 - len as i64 + 1) as i32;
    for _ in 0..len {
        nums.push(cur);
        if cur < 100000 {
            let step = rng.gen_range_i64(0, 3.min((100000 - cur as i64).max(0))) as i32;
            cur = cur + step;
        }
    }
    nums
}

/// Build a monotone decreasing array of given length with values in [-100000, 100000].
fn build_decreasing(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    let mut cur = rng.gen_range_i64(-100000 + len as i64 - 1, 100000) as i32;
    for _ in 0..len {
        nums.push(cur);
        if cur > -100000 {
            let step = rng.gen_range_i64(0, 3.min((cur as i64 + 100000).max(0))) as i32;
            cur = cur - step;
        }
    }
    nums
}

/// Build a random (non-monotonic) array.
fn build_random(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(-100000, 100000) as i32);
    }
    nums
}

/// Build a constant array.
fn build_constant(rng: &mut Rng, len: usize) -> Vec<i32> {
    let val = rng.gen_range_i64(-100000, 100000) as i32;
    vec![val; len]
}

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    // Example test cases from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 2, 3],
        vec![6, 5, 4, 4],
        vec![1, 3, 2],
    ];
    for nums in examples {
        let result = Solution::is_monotonic(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
    }

    let num_mutations: u8 = 12;

    for i in 0..count {
        // Size classes
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10000),  // big (capped for speed)
        };

        // Build base array with structural diversity
        let base = match i % 4 {
            0 => build_increasing(&mut rng, n),
            1 => build_decreasing(&mut rng, n),
            2 => build_random(&mut rng, n),
            _ => build_constant(&mut rng, n),
        };

        // Apply mutation
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let nums = mutate(base, mk);

        let result = Solution::is_monotonic(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
    }
}
