use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 1 (boundary low)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 2 {
        // set last element to 100 (boundary high)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 100);
        d
    } else if mutation_kind == 3 && nums.len() < 100 {
        // grow: push element 1
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 4 && nums.len() > 1 {
        // shrink: pop last element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 5 {
        // set first element to 1
        let mut d = nums;
        d.set(0, 1);
        d
    } else if mutation_kind == 6 {
        // set first element to 100
        let mut d = nums;
        d.set(0, 100);
        d
    } else if mutation_kind == 7 {
        // nudge last element up (if < 100)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 100 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 8 {
        // nudge last element down (if > 1)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        d
    } else if mutation_kind == 10 {
        // set all elements to 50
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 50,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 50);
            i += 1;
        }
        d
    } else if mutation_kind == 11 && nums.len() < 100 {
        // grow: push element 100
        let mut d = nums;
        d.push(100);
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100) as i32);
    }
    nums
}

// Build an alternating-parity array (special array)
fn alternating_nums(rng: &mut Rng, len: usize, start_even: bool) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for i in 0..len {
        let even = if start_even { i % 2 == 0 } else { i % 2 == 1 };
        if even {
            nums.push(rng.gen_range_i64(1, 50) as i32 * 2); // even: 2..100
        } else {
            nums.push(rng.gen_range_i64(0, 49) as i32 * 2 + 1); // odd: 1..99
        }
    }
    nums
}

// Build a same-parity array (not special for len > 1)
fn same_parity_nums(rng: &mut Rng, len: usize, even: bool) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        if even {
            nums.push(rng.gen_range_i64(1, 50) as i32 * 2);
        } else {
            nums.push(rng.gen_range_i64(0, 49) as i32 * 2 + 1);
        }
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3151);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::is_array_special(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1],
        vec![2, 1, 4],
        vec![4, 3, 1, 6],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Curated seeds: boundary values and interesting patterns
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],                         // single element, min value
        vec![100],                       // single element, max value
        vec![1, 2],                      // two elements, special
        vec![1, 3],                      // two elements, not special (both odd)
        vec![2, 4],                      // two elements, not special (both even)
        vec![2, 1, 4, 3],               // alternating even-odd
        vec![1, 2, 3, 4, 5],            // alternating odd-even
        vec![2, 2, 2, 2],               // all same even
        vec![1, 1, 1, 1],               // all same odd
        vec![99, 100],                   // boundary values, special
        vec![99, 100, 1, 2],            // boundary pairs
        vec![50, 51, 50, 51],           // mid-range alternating
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Apply every mutation to every seed
    for seed in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Generate alternating-parity arrays (should be special)
    for _ in 0..15 {
        let len = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_usize(2, 5),
            2 => rng.gen_range_usize(6, 20),
            3 => rng.gen_range_usize(21, 50),
            _ => rng.gen_range_usize(51, 100),
        };
        let start_even = rng.gen_range_usize(0, 1) == 0;
        let nums = alternating_nums(&mut rng, len, start_even);
        let mk = rng.gen_range_usize(0, 11) as u8;
        emit(mutate(nums, mk), &mut seen, &mut out, &mut count);
    }

    // Generate same-parity arrays (should not be special for len > 1)
    for _ in 0..10 {
        let len = rng.gen_range_usize(2, 50);
        let even = rng.gen_range_usize(0, 1) == 0;
        let nums = same_parity_nums(&mut rng, len, even);
        let mk = rng.gen_range_usize(0, 11) as u8;
        emit(mutate(nums, mk), &mut seen, &mut out, &mut count);
    }

    // Random arrays with random mutations
    while count < target_count {
        let len = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_usize(1, 5),
            2 => rng.gen_range_usize(6, 20),
            3 => rng.gen_range_usize(21, 50),
            _ => rng.gen_range_usize(51, 100),
        };
        let nums = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 11) as u8;
        emit(mutate(nums, mk), &mut seen, &mut out, &mut count);
    }
}
