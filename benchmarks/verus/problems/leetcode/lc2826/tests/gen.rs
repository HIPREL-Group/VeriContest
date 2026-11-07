use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 3,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 3,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set all elements to 1
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 2 {
        // set all elements to 2
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 2,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 2);
            i += 1;
        }
        d
    } else if mutation_kind == 3 {
        // set all elements to 3
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 3,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 3);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && nums.len() < 100 {
        // grow by one element (push a 1)
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 5 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 6 {
        // nudge first element: cycle 1->2->3->1
        let mut d = nums;
        let new_val: i32 = if d[0] == 3 { 1 } else { d[0] + 1 };
        d.set(0, new_val);
        d
    } else if mutation_kind == 7 {
        // nudge last element: cycle 1->2->3->1
        let mut d = nums;
        let last = d.len() - 1;
        let new_val: i32 = if d[last] == 3 { 1 } else { d[last] + 1 };
        d.set(last, new_val);
        d
    } else if mutation_kind == 8 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let tmp = d[0];
        d.set(0, d[last]);
        d.set(last, tmp);
        d
    } else if mutation_kind == 9 {
        // set first element to 1, last element to 3 (sorted endpoints)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(0, 1);
        d.set(last, 3);
        d
    } else {
        nums // fallback
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
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 3) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2826);
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
        let output = Solution::minimum_operations(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from the problem description
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 1, 3, 2, 1],
        vec![1, 3, 2, 1, 3, 3],
        vec![2, 2, 2, 2, 3, 3],
    ];

    // Additional structured seeds
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![2],
        vec![3],
        vec![1, 2, 3],
        vec![3, 2, 1],
        vec![1, 1, 1, 1, 1],
        vec![3, 3, 3, 3, 3],
        vec![1, 2, 2, 3, 3, 3],
        vec![3, 1, 2, 3, 1, 2],
        vec![1, 3, 1, 3, 1, 3],
        vec![2, 1, 2, 1, 2, 1],
        vec![1, 1, 2, 2, 3, 3],
        vec![3, 3, 2, 2, 1, 1],
        vec![1, 2, 1, 2, 1, 2, 1, 2, 1, 2],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Emit examples with identity mutation
    for ex in &examples {
        emit(generate_test_case(ex.clone(), 0), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = generate_test_case(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target {
        let len: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 30),      // medium
            3 => rng.gen_range_usize(31, 70),      // large
            _ => rng.gen_range_usize(71, 100),     // max
        };
        let s = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = generate_test_case(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
