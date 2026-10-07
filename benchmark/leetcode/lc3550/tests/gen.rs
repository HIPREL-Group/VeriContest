use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut r = nums;
        let last = r.len() - 1;
        r.set(last, 0);
        r
    } else if mutation_kind == 2 {
        // set last element to 1000 (max boundary)
        let mut r = nums;
        let last = r.len() - 1;
        r.set(last, 1000);
        r
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut r = nums;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == nums.len(),
                1 <= r.len() <= 100,
                forall|j: int| 0 <= j < i ==> r[j] == 0i32,
                forall|j: int| i <= j < r.len() ==> r[j] == nums[j],
            decreases r.len() - i,
        {
            r.set(i, 0);
            i += 1;
        }
        r
    } else if mutation_kind == 4 && nums.len() < 100 {
        // grow by one element (push 0)
        let mut r = nums;
        r.push(0);
        r
    } else if mutation_kind == 5 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut r = nums;
        r.pop();
        r
    } else if mutation_kind == 6 {
        // nudge first element up: if < 1000, increment by 1
        let mut r = nums;
        if r[0] < 1000 {
            r.set(0, r[0] + 1);
        }
        r
    } else if mutation_kind == 7 {
        // nudge first element down: if > 0, decrement by 1
        let mut r = nums;
        if r[0] > 0 {
            r.set(0, r[0] - 1);
        }
        r
    } else if mutation_kind == 8 {
        // set first element to its digit sum (makes digit_sum(nums[0]) small)
        let mut r = nums;
        let v = r[0];
        let ds = v / 1000 + (v / 100) % 10 + (v / 10) % 10 + v % 10;
        r.set(0, ds);
        assert(0 <= ds <= 28) by {
            assert(0 <= v <= 1000);
            assert(0 <= v / 1000 <= 1);
            assert(0 <= (v / 100) % 10 <= 9);
            assert(0 <= (v / 10) % 10 <= 9);
            assert(0 <= v % 10 <= 9);
        }
        r
    } else if mutation_kind == 9 {
        // set all elements to the same value as the first
        let mut r = nums;
        let val = r[0];
        let mut i: usize = 1;
        while i < r.len()
            invariant
                1 <= i <= r.len(),
                r.len() == nums.len(),
                1 <= r.len() <= 100,
                0 <= val <= 1000,
                forall|j: int| 0 <= j < i ==> r[j] == val,
                forall|j: int| i <= j < r.len() ==> r[j] == nums[j],
            decreases r.len() - i,
        {
            r.set(i, val);
            i += 1;
        }
        r
    } else {
        // fallback
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
        nums.push(rng.gen_range_i64(0, 1000) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3550);
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
        let output = Solution::smallest_index(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 3, 2],       // expected output: 2
        vec![1, 10, 11],     // expected output: 1
        vec![1, 2, 3],       // expected output: -1
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted interesting cases
    let interesting: Vec<Vec<i32>> = vec![
        vec![0],                           // digit_sum(0)=0, index 0 → match
        vec![1],                           // digit_sum(1)=1, index 0 → no match
        vec![0, 1, 2, 3, 4],              // every index matches
        vec![999],                         // digit_sum(999)=27, index 0 → no
        vec![1000],                        // digit_sum(1000)=1, index 0 → no
        vec![5, 0],                        // no match
        vec![0, 0],                        // match at index 0
        vec![100, 1, 2, 3],               // digit_sum(100)=1≠0, digit_sum(1)=1=1 → match at 1
        vec![10, 10, 2],                   // digit_sum(10)=1≠0, digit_sum(10)=1=1 → match at 1
    ];
    for case in &interesting {
        emit(case.clone(), &mut seen, &mut out, &mut count);
    }

    // Seed pool with mutations
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
        vec![1000; 10],
        vec![0; 100],
        vec![500; 50],
        vec![10, 20, 30],
        vec![0, 1],
        vec![999, 999, 999],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    for seed_arr in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random arrays with random mutations across diverse size classes
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 5),     // tiny
            1 => rng.gen_range_usize(1, 10),    // small
            2 => rng.gen_range_usize(11, 30),   // medium
            3 => rng.gen_range_usize(31, 70),   // large
            _ => rng.gen_range_usize(71, 100),  // max
        };
        let nums = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(nums, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
