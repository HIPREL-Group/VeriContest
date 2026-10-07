use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= nums.len() <= 1000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
    ensures
        2 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut d = nums;
        d.set(0, 1);
        d
    } else if mutation_kind == 2 {
        // set first element to 1000 (max boundary)
        let mut d = nums;
        d.set(0, 1000);
        d
    } else if mutation_kind == 3 {
        // set last element to 1 (min boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 4 {
        // set last element to 1000 (max boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1000);
        d
    } else if mutation_kind == 5 && nums.len() < 1000 {
        // grow by one element (push 500)
        let mut d = nums;
        d.push(500);
        d
    } else if mutation_kind == 6 && nums.len() > 2 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 7 {
        // set all elements to the same value (tests non-strictly-increasing)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                2 <= d.len() <= 1000,
                forall|j: int| 0 <= j < i ==> d[j] == 500,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 500);
            i += 1;
        }
        d
    } else if mutation_kind == 8 && nums.len() >= 3 {
        // swap first two elements
        let mut d = nums;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
        d
    } else if mutation_kind == 9 {
        // nudge first element: if < 1000 increment, else decrement
        let mut d = nums;
        if d[0] < 1000 {
            d.set(0, d[0] + 1);
        } else {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 10 {
        // nudge last element: if > 1 decrement, else increment
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        } else {
            d.set(last, d[last] + 1);
        }
        d
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
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 1000) as i32);
    }
    nums
}

fn sorted_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    // Generate a strictly increasing array
    let mut nums = Vec::with_capacity(len);
    let mut val = rng.gen_range_i64(1, 10) as i32;
    for _ in 0..len {
        nums.push(val);
        let step = rng.gen_range_i64(1, 5) as i32;
        val = std::cmp::min(val.saturating_add(step), 1000);
    }
    nums
}

fn almost_sorted_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    // Generate a strictly increasing array, then break one position
    let mut nums = sorted_nums(rng, len);
    if len >= 2 {
        let pos = rng.gen_range_usize(0, len - 1);
        nums[pos] = rng.gen_range_i64(1, 1000) as i32;
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1909);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::can_be_increasing(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from the problem description
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 10, 5, 7],   // true
        vec![2, 3, 1, 2],       // false
        vec![1, 1, 1],          // false
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Interesting seed arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 2],                     // minimal, already strictly increasing
        vec![2, 1],                     // minimal, reversed
        vec![1, 1],                     // minimal, equal
        vec![1, 2, 3],                  // already sorted
        vec![3, 2, 1],                  // fully reversed
        vec![1, 3, 2],                  // one swap from sorted
        vec![1, 2, 3, 4, 5],           // fully sorted
        vec![5, 1, 2, 3, 4],           // one element out of place at start
        vec![1, 2, 3, 4, 1],           // one element out of place at end
        vec![1, 1000],                  // boundary values
        vec![1000, 1],                  // boundary values reversed
        vec![1, 500, 1000],             // spread
        vec![1, 2, 1000, 3, 4],        // spike in middle
        vec![500, 500, 500],            // all same
    ];

    let mutation_kinds: Vec<u8> = (0..=10).collect();

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Apply mutations to example inputs
    for ex in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Sorted arrays of various sizes with mutations
    for _ in 0..20 {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 5),       // tiny
            1 => rng.gen_range_usize(2, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 500),    // large
            _ => rng.gen_range_usize(501, 1000),   // max
        };
        let s = sorted_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 10) as u8;
        emit(mutate(s, mk), &mut seen, &mut out, &mut count);
    }

    // Almost-sorted arrays (one element disrupted)
    for _ in 0..20 {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };
        let s = almost_sorted_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 10) as u8;
        emit(mutate(s, mk), &mut seen, &mut out, &mut count);
    }

    // Random arrays with random mutations
    for _ in 0..40 {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };
        let s = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 10) as u8;
        emit(mutate(s, mk), &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random arrays, identity mutation
    while count < count_target {
        let n = rng.gen_range_usize(2, 1000);
        let s = random_nums(&mut rng, n);
        emit(mutate(s, 0), &mut seen, &mut out, &mut count);
    }
}
