use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= values.len() <= 100_000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
        1 <= k <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < values.len()
            invariant
                0 <= i <= values.len(),
                nums.len() == i,
                1 <= values.len() <= 100_000,
                forall|j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> nums[j] == values[j],
                forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1_000_000_000,
            decreases values.len() - i,
        {
            nums.push(values[i]);
            i += 1;
        }
        (nums, k)
    } else if mutation_kind == 1 && values.len() > 1 {
        // shrink -- drop last element
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let new_len: usize = values.len() - 1;
        while i < new_len
            invariant
                0 <= i <= new_len,
                new_len == values.len() - 1,
                new_len >= 1,
                nums.len() == i,
                1 <= values.len() <= 100_000,
                forall|j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> nums[j] == values[j],
                forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1_000_000_000,
            decreases new_len - i,
        {
            nums.push(values[i]);
            i += 1;
        }
        (nums, k)
    } else if mutation_kind == 2 && values.len() < 100_000 {
        // grow -- duplicate last element
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < values.len()
            invariant
                0 <= i <= values.len(),
                nums.len() == i,
                1 <= values.len() < 100_000,
                forall|j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> nums[j] == values[j],
                forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1_000_000_000,
            decreases values.len() - i,
        {
            nums.push(values[i]);
            i += 1;
        }
        let last_val = values[values.len() - 1];
        nums.push(last_val);
        (nums, k)
    } else if mutation_kind == 3 {
        // set first element to 1 (min boundary)
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < values.len()
            invariant
                0 <= i <= values.len(),
                nums.len() == i,
                1 <= values.len() <= 100_000,
                forall|j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < i && j == 0 ==> nums[j] == 1i32,
                forall|j: int| 0 <= j < i && j > 0 ==> nums[j] == values[j],
                forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1_000_000_000,
            decreases values.len() - i,
        {
            if i == 0 {
                nums.push(1i32);
            } else {
                nums.push(values[i]);
            }
            i += 1;
        }
        (nums, k)
    } else if mutation_kind == 4 {
        // set first element to max boundary
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < values.len()
            invariant
                0 <= i <= values.len(),
                nums.len() == i,
                1 <= values.len() <= 100_000,
                forall|j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < i && j == 0 ==> nums[j] == 1_000_000_000i32,
                forall|j: int| 0 <= j < i && j > 0 ==> nums[j] == values[j],
                forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1_000_000_000,
            decreases values.len() - i,
        {
            if i == 0 {
                nums.push(1_000_000_000i32);
            } else {
                nums.push(values[i]);
            }
            i += 1;
        }
        (nums, k)
    } else if mutation_kind == 5 {
        // set all elements to 1
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < values.len()
            invariant
                0 <= i <= values.len(),
                nums.len() == i,
                1 <= values.len() <= 100_000,
                forall|j: int| 0 <= j < nums.len() ==> #[trigger] nums[j] == 1i32,
                forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1_000_000_000,
            decreases values.len() - i,
        {
            nums.push(1i32);
            i += 1;
        }
        (nums, k)
    } else if mutation_kind == 6 && k < 1_000_000_000 {
        // nudge k up
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < values.len()
            invariant
                0 <= i <= values.len(),
                nums.len() == i,
                1 <= values.len() <= 100_000,
                forall|j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> nums[j] == values[j],
            decreases values.len() - i,
        {
            nums.push(values[i]);
            i += 1;
        }
        (nums, k + 1)
    } else if mutation_kind == 7 && k > 1 {
        // nudge k down
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < values.len()
            invariant
                0 <= i <= values.len(),
                nums.len() == i,
                1 <= values.len() <= 100_000,
                forall|j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> nums[j] == values[j],
            decreases values.len() - i,
        {
            nums.push(values[i]);
            i += 1;
        }
        (nums, k - 1)
    } else if mutation_kind == 8 {
        // k = 1 (min boundary for k)
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < values.len()
            invariant
                0 <= i <= values.len(),
                nums.len() == i,
                1 <= values.len() <= 100_000,
                forall|j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> nums[j] == values[j],
            decreases values.len() - i,
        {
            nums.push(values[i]);
            i += 1;
        }
        (nums, 1i32)
    } else {
        // fallback -- identity
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < values.len()
            invariant
                0 <= i <= values.len(),
                nums.len() == i,
                1 <= values.len() <= 100_000,
                forall|j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> nums[j] == values[j],
                forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1_000_000_000,
            decreases values.len() - i,
        {
            nums.push(values[i]);
            i += 1;
        }
        (nums, k)
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

fn mutate(values: &Vec<i32>, k: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(values, k, mutation_kind)
}

fn random_values(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut vals = Vec::with_capacity(len);
    for _ in 0..len {
        vals.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    vals
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
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
        let key = format!("{:?}:{}", nums, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::max_operations(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![1, 2, 3, 4], 5, &mut seen, &mut out, &mut count);
    emit(vec![3, 1, 3, 4, 3], 6, &mut seen, &mut out, &mut count);

    // Seed inputs with interesting structure
    let seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 1),
        (vec![1, 1], 2),
        (vec![1, 1_000_000_000], 1_000_000_001),
        (vec![500_000_000, 500_000_000], 1_000_000_000),
        (vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 11),
        (vec![1, 1, 1, 1, 1], 2),
        (vec![5, 5, 5, 5], 10),
        (vec![1, 2, 3, 4, 5], 100),
        (vec![1, 999_999_999], 1_000_000_000),
        (vec![2, 2, 2, 2, 2, 2], 4),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    for (vals, k) in &seeds {
        for &mk in &mutation_kinds {
            let (nums, k_out) = mutate(vals, *k, mk);
            emit(nums, k_out, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with varied sizes
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 5),
        (6, 20),
        (21, 100),
        (101, 1000),
        (1001, 5000),
    ];

    for (lo, hi) in &size_classes {
        for _ in 0..10 {
            let len = rng.gen_range_usize(*lo, *hi);
            let k = rng.gen_range_i64(1, 1_000_000_000) as i32;
            let vals = random_values(&mut rng, len);
            let mk = rng.gen_range_usize(0, 8) as u8;
            let (nums, k_out) = mutate(&vals, k, mk);
            emit(nums, k_out, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 5000),
        };
        let k = if count % 5 == 0 {
            let boundary_vals = [1i32, 2, 1_000_000_000, 999_999_999];
            boundary_vals[count % 4]
        } else {
            rng.gen_range_i64(1, 1_000_000_000) as i32
        };
        let vals = random_values(&mut rng, len);
        let (nums, k_out) = mutate(&vals, k, 0);
        emit(nums, k_out, &mut seen, &mut out, &mut count);
    }
}
