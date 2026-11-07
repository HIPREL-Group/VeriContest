use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 2_000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
    ensures
        1 <= result.len() <= 2_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to an even value (0)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 2 {
        // set all elements to the same even value (2)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 2_000,
                forall|j: int| 0 <= j < i ==> d[j] == 2,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 2);
            i += 1;
        }
        d
    } else if mutation_kind == 3 {
        // set all elements to odd values (1) — triggers -1 result
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 2_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && nums.len() < 2_000 {
        // grow by one element (push even value 4)
        let mut d = nums;
        d.push(4);
        d
    } else if mutation_kind == 5 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 6 {
        // set first element to max boundary (100_000, which is even)
        let mut d = nums;
        d.set(0, 100_000);
        d
    } else if mutation_kind == 7 {
        // nudge last element: if < 100_000, increment by 1
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 100_000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 8 {
        // set last element to max boundary 100_000
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 100_000);
        d
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
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

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(0, 100_000) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2404);
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
        let output = Solution::most_frequent_even(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![0, 1, 2, 2, 4, 4, 1],
        vec![4, 4, 4, 9, 2, 4],
        vec![29, 47, 21, 41, 13, 37, 25, 7],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Curated seeds
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1],
        vec![2],
        vec![100_000],
        vec![99_999],
        vec![0, 0],
        vec![1, 1],
        vec![2, 4],
        vec![0, 2, 4, 6, 8],
        vec![1, 3, 5, 7, 9],
        vec![2, 2, 2, 3, 3, 3],
        vec![2, 4, 2, 4],
        vec![100_000, 100_000, 99_998],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            emit(mutate(s.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with random mutations across size classes
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 500),   // large
            _ => rng.gen_range_usize(501, 2_000), // max
        };
        let nums = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        emit(mutate(nums, mk), &mut seen, &mut out, &mut count);
    }
}
