use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: &mut Vec<i32>, mutation_kind: u8)
    requires
        1 <= old(nums).len() <= 50_000,
        forall|i: int| 0 <= i < old(nums).len() ==> 0 <= #[trigger] old(nums)[i] <= 10_000,
    ensures
        1 <= old(nums).len() <= 50_000,
        forall|i: int| 0 <= i < old(nums).len() ==> 0 <= #[trigger] old(nums)[i] <= 10_000,
        1 <= nums.len() <= 50_000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 10_000,
{
    if mutation_kind == 0 {
        // identity — no changes
    } else if mutation_kind == 1 {
        // set first element to 0
        nums.set(0, 0);
    } else if mutation_kind == 2 {
        // set first element to 10_000 (max boundary)
        nums.set(0, 10_000);
    } else if mutation_kind == 3 {
        // set last element to 0
        let last = nums.len() - 1;
        nums.set(last, 0);
    } else if mutation_kind == 4 {
        // set last element to 10_000
        let last = nums.len() - 1;
        nums.set(last, 10_000);
    } else if mutation_kind == 5 {
        // set all elements to 0
        let n = nums.len();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                1 <= nums.len() <= 50_000,
                forall|j: int| 0 <= j < i ==> nums[j] == 0i32,
                forall|j: int| i <= j < n ==> nums[j] == old(nums)[j],
            decreases n - i,
        {
            nums.set(i, 0);
            i += 1;
        }
    } else if mutation_kind == 6 {
        // set all elements to 10_000
        let n = nums.len();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                1 <= nums.len() <= 50_000,
                forall|j: int| 0 <= j < i ==> nums[j] == 10_000i32,
                forall|j: int| i <= j < n ==> nums[j] == old(nums)[j],
            decreases n - i,
        {
            nums.set(i, 10_000);
            i += 1;
        }
    } else if mutation_kind == 7 && nums.len() < 50_000 {
        // grow by one element (push 0)
        nums.push(0);
    } else if mutation_kind == 8 && nums.len() > 1 {
        // shrink by one element (pop)
        nums.pop();
    } else if mutation_kind == 9 && nums[0] < 10_000 {
        // nudge first element up
        nums.set(0, nums[0] + 1);
    } else if mutation_kind == 10 && nums[0] > 0 {
        // nudge first element down
        nums.set(0, nums[0] - 1);
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 10_000) as i32);
    }
    v
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums_input: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let key = format!("{:?}", nums_input);
        if *count >= goal || !seen.insert(key) {
            return;
        }
        let mut nums = nums_input.clone();
        Solution::wiggle_sort(&mut nums);
        writeln!(out, "{}", json!({"input": {"nums": nums_input}, "output": nums})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![3, 5, 2, 1, 6, 4],
        vec![6, 6, 5, 6, 3, 8],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Seed arrays: boundary and interesting cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![10_000],
        vec![1],
        vec![0, 0],
        vec![10_000, 10_000],
        vec![0, 10_000],
        vec![10_000, 0],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![5, 5, 5, 5, 5],
        vec![0, 0, 0, 0, 0],
        vec![10_000, 10_000, 10_000],
        vec![1, 1, 1, 1],
        vec![0, 1, 0, 1, 0],
    ];

    let mutation_kinds: Vec<u8> = (0..=10).collect();

    // Apply every mutation to every seed
    for seed_arr in &seeds {
        for &mk in &mutation_kinds {
            if count >= goal { break; }
            let mut arr = seed_arr.clone();
            generate_test_case(&mut arr, mk);
            emit(arr, &mut seen, &mut out, &mut count);
        }
        if count >= goal { break; }
    }

    // Generate diverse random arrays across size classes
    for i in 0..200usize {
        if count >= goal { break; }
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 5000),   // big
        };
        let mut arr = random_nums(&mut rng, n);
        let mk = rng.gen_u8() % 11;
        generate_test_case(&mut arr, mk);
        emit(arr, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random arrays, identity mutation
    while count < goal {
        let n = rng.gen_range_usize(1, 10_000);
        let mut arr = random_nums(&mut rng, n);
        generate_test_case(&mut arr, 0);
        emit(arr, &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
