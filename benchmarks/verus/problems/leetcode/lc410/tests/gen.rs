use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    elements: Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= elements.len() <= 1_000,
        forall|i: int| 0 <= i < elements.len() ==> 0 <= #[trigger] elements[i] <= 1_000_000,
        1 <= k <= 50,
        k <= elements.len(),
    ensures
        1 <= result.0.len() <= 1_000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1_000_000,
        1 <= result.1 <= 50,
        result.1 <= result.0.len(),
{
    if mutation_kind == 0 {
        // identity
        (elements, k)
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut nums = elements;
        let last = nums.len() - 1;
        nums.set(last, 0);
        (nums, k)
    } else if mutation_kind == 2 {
        // set last element to 1_000_000 (max boundary)
        let mut nums = elements;
        let last = nums.len() - 1;
        nums.set(last, 1_000_000);
        (nums, k)
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut nums = elements;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() == elements.len(),
                1 <= nums.len() <= 1_000,
                forall|j: int| 0 <= j < i ==> nums[j] == 0i32,
                forall|j: int| i <= j < nums.len() ==> nums[j] == elements[j],
            decreases nums.len() - i,
        {
            nums.set(i, 0);
            i += 1;
        }
        (nums, k)
    } else if mutation_kind == 4 {
        // set all elements to 1_000_000
        let mut nums = elements;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() == elements.len(),
                1 <= nums.len() <= 1_000,
                forall|j: int| 0 <= j < i ==> nums[j] == 1_000_000i32,
                forall|j: int| i <= j < nums.len() ==> nums[j] == elements[j],
            decreases nums.len() - i,
        {
            nums.set(i, 1_000_000);
            i += 1;
        }
        (nums, k)
    } else if mutation_kind == 5 && k < 50 && (k + 1) as usize <= elements.len() {
        // nudge k up by 1
        (elements, k + 1)
    } else if mutation_kind == 6 && k > 1 {
        // nudge k down by 1
        (elements, k - 1)
    } else if mutation_kind == 7 {
        // set k = 1
        (elements, 1)
    } else if mutation_kind == 8 {
        // set k = nums.len() (each element is its own subarray)
        let k_new: i32 = if elements.len() <= 50 {
            elements.len() as i32
        } else {
            50
        };
        (elements, k_new)
    } else if mutation_kind == 9 {
        // nudge first element: if < 1_000_000, increment
        let mut nums = elements;
        if nums[0] < 1_000_000 {
            nums.set(0, nums[0] + 1);
        }
        (nums, k)
    } else if mutation_kind == 10 {
        // nudge first element down: if > 0, decrement
        let mut nums = elements;
        if nums[0] > 0 {
            nums.set(0, nums[0] - 1);
        }
        (nums, k)
    } else if mutation_kind == 11 && elements.len() > 1 {
        // shrink array by one (pop), adjust k if needed
        let mut nums = elements;
        nums.pop();
        let k_new = if k as usize > nums.len() {
            nums.len() as i32
        } else {
            k
        };
        assert(1 <= k_new);
        (nums, k_new)
    } else if mutation_kind == 12 && elements.len() < 1_000 {
        // grow array by one (push 0)
        let mut nums = elements;
        nums.push(0);
        (nums, k)
    } else {
        // fallback: identity
        (elements, k)
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(0, 1_000_000) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(410);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}_{}", nums, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::split_array(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![7, 2, 5, 10, 8], 2),
        (vec![1, 2, 3, 4, 5], 2),
    ];
    for (nums, k) in examples {
        emit(nums, k, &mut seen, &mut out, &mut count);
    }

    // Seed inputs with diverse properties
    let seed_inputs: Vec<(Vec<i32>, i32)> = vec![
        (vec![0], 1),
        (vec![1_000_000], 1),
        (vec![0, 0, 0, 0, 0], 3),
        (vec![1_000_000, 1_000_000, 1_000_000], 3),
        (vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 5),
        (vec![100, 200, 300, 400, 500], 1),
        (vec![100, 200, 300, 400, 500], 5),
        (vec![10, 20, 30, 40, 50, 60, 70, 80, 90, 100], 3),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];

    // Apply every mutation to seed inputs
    for (nums, k) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (result_nums, result_k) = generate_test_case(nums.clone(), *k, mk);
            emit(result_nums, result_k, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs across size classes with random mutations
    for i in 0..200 {
        if count >= target { break; }
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 50),       // medium
            3 => rng.gen_range_usize(51, 200),      // large
            _ => rng.gen_range_usize(201, 1000),    // max
        };
        let nums = random_nums(&mut rng, n);
        let max_k = std::cmp::min(50, n) as i64;
        let k = rng.gen_range_i64(1, max_k) as i32;
        let mk = rng.gen_range_usize(0, 12) as u8;
        let (result_nums, result_k) = generate_test_case(nums, k, mk);
        emit(result_nums, result_k, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with identity mutations on random inputs
    while count < target {
        let n = rng.gen_range_usize(1, 1000);
        let nums = random_nums(&mut rng, n);
        let max_k = std::cmp::min(50, n) as i64;
        let k = rng.gen_range_i64(1, max_k) as i32;
        let (result_nums, result_k) = generate_test_case(nums, k, 0);
        emit(result_nums, result_k, &mut seen, &mut out, &mut count);
    }
}
