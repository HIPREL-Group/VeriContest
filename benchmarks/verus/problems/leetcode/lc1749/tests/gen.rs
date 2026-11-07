use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> -10000 <= #[trigger] nums[i] <= 10000,
    ensures
        1 <= result@.len() <= 100000,
        forall|i: int| 0 <= i < result@.len() ==> -10000 <= #[trigger] result[i] <= 10000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 10000 (max boundary)
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 10000);
        v
    } else if mutation_kind == 2 {
        // set last element to -10000 (min boundary)
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, -10000);
        v
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 0);
        v
    } else if mutation_kind == 4 {
        // negate last element
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, -v[last]);
        v
    } else if mutation_kind == 5 && nums.len() < 100000 {
        // grow by one element (push 0)
        let mut v = nums;
        v.push(0);
        v
    } else if mutation_kind == 6 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut v = nums;
        v.pop();
        v
    } else if mutation_kind == 7 {
        // set all elements to 0
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 100000,
                forall|j: int| 0 <= j < i ==> v[j] == 0i32,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, 0);
            i += 1;
        }
        v
    } else if mutation_kind == 8 {
        // set all elements to 10000
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 100000,
                forall|j: int| 0 <= j < i ==> v[j] == 10000i32,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, 10000);
            i += 1;
        }
        v
    } else if mutation_kind == 9 {
        // set all elements to -10000
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 100000,
                forall|j: int| 0 <= j < i ==> v[j] == -10000i32,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, -10000);
            i += 1;
        }
        v
    } else if mutation_kind == 10 {
        // nudge last element up (if < 10000)
        let mut v = nums;
        let last = v.len() - 1;
        if v[last] < 10000 {
            v.set(last, v[last] + 1);
        }
        v
    } else if mutation_kind == 11 {
        // nudge last element down (if > -10000)
        let mut v = nums;
        let last = v.len() - 1;
        if v[last] > -10000 {
            v.set(last, v[last] - 1);
        }
        v
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

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(-10000, 10000) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut rng = Rng::new(seed);
    let mut generated = 0usize;

    // Example 1: [1,-3,2,3,-4] -> 5
    {
        let nums = vec![1, -3, 2, 3, -4];
        let result = Solution::max_absolute_sum(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
        generated += 1;
    }

    // Example 2: [2,-5,1,-4,3,-2] -> 8
    {
        let nums = vec![2, -5, 1, -4, 3, -2];
        let result = Solution::max_absolute_sum(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
        generated += 1;
    }

    // Edge cases
    let edge_cases: Vec<Vec<i32>> = vec![
        vec![0],
        vec![10000],
        vec![-10000],
        vec![10000, -10000],
        vec![-10000, 10000],
        vec![0, 0, 0],
        vec![1, 1, 1, 1, 1],
        vec![-1, -1, -1, -1, -1],
    ];
    for nums in edge_cases {
        let result = Solution::max_absolute_sum(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
        generated += 1;
    }

    let num_mutations: u8 = 12;

    while generated < count {
        // Size classes
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // big
        };

        let base_nums = random_nums(&mut rng, n);
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let nums = generate_test_case(base_nums, mk);
        let result = Solution::max_absolute_sum(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
        generated += 1;
    }
}
