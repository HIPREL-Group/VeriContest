use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 50,
        forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
    ensures
        1 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() ==> -1000 <= #[trigger] result[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 && nums.len() < 50 {
        // grow: append 0
        let mut d = nums;
        d.push(0);
        d
    } else if mutation_kind == 2 && nums.len() > 1 {
        // shrink: remove last element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 4 {
        // set last element to 1000 (max boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1000);
        d
    } else if mutation_kind == 5 {
        // set last element to -1000 (min boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, -1000);
        d
    } else if mutation_kind == 6 {
        // nudge last element up
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 1000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 7 {
        // nudge last element down
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > -1000 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 8 {
        // set all elements to the same value (first element)
        let val = nums[0];
        let n = nums.len();
        let mut d = nums;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                d.len() == n,
                1 <= n <= 50,
                -1000 <= val <= 1000,
                forall|j: int| 0 <= j < i as int ==> d[j] == val,
                forall|j: int| i as int <= j < n as int ==> d[j] == nums[j],
            decreases n - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        d
    } else if mutation_kind == 10 {
        // negate last element
        let mut d = nums;
        let last = d.len() - 1;
        let v = d[last];
        if v > -1000 {
            d.set(last, -v);
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
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(-1000, 1000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3507);
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
        let output = Solution::minimum_pair_removal(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![5, 2, 3, 1],
        vec![1, 2, 2],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Emit examples with identity mutation first
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Curated seed inputs covering interesting cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1000],
        vec![-1000],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![0, 0, 0, 0],
        vec![1000, -1000],
        vec![-1000, 1000],
        vec![1, -1, 1, -1],
        vec![999, 1000],
        vec![-999, -1000],
        vec![500, 500, 500],
        vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
        vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1],
    ];

    // Apply every mutation to every seed
    for seed_arr in &seeds {
        for &mk in &mutation_kinds {
            let result = generate_test_case(seed_arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across diverse size classes
    while count < target {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(4, 10),       // small
            2 => rng.gen_range_usize(11, 25),      // medium
            3 => rng.gen_range_usize(26, 40),      // large
            _ => rng.gen_range_usize(41, 50),      // max
        };
        let seed_arr = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = generate_test_case(seed_arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
