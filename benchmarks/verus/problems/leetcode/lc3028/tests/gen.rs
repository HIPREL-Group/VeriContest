use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> -10 <= #[trigger] nums[i] <= 10,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] != 0,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> -10 <= #[trigger] result[i] <= 10,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] != 0,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // negate all elements
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> -10 <= #[trigger] d[j] <= 10,
                forall|j: int| 0 <= j < i ==> #[trigger] d[j] != 0,
                forall|j: int| i <= j < d.len() ==> -10 <= #[trigger] d[j] <= 10,
                forall|j: int| i <= j < d.len() ==> #[trigger] d[j] != 0,
            decreases d.len() - i,
        {
            let old_val = d[i];
            d.set(i, -old_val);
            i += 1;
        }
        d
    } else if mutation_kind == 2 {
        // set last element to 1
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 3 {
        // set last element to -1
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, -1);
        d
    } else if mutation_kind == 4 {
        // set first element to 10
        let mut d = nums;
        d.set(0, 10);
        d
    } else if mutation_kind == 5 {
        // set first element to -10
        let mut d = nums;
        d.set(0, -10);
        d
    } else if mutation_kind == 6 && nums.len() < 100 {
        // grow: append element 1
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 7 && nums.len() > 1 {
        // shrink: remove last element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 8 {
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
    } else if mutation_kind == 9 {
        // set all elements to -1
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == -1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, -1);
            i += 1;
        }
        d
    } else if mutation_kind == 10 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        d
    } else if mutation_kind == 11 {
        // nudge last element toward zero (keep non-zero)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        } else if d[last] < -1 {
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

fn random_nonzero_vec(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        let mut val = rng.gen_range_i64(-10, 10) as i32;
        if val == 0 { val = 1; }
        v.push(val);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3028);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::return_to_boundary_count(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 3, -5],
        vec![3, 2, -3, -4],
    ];

    let mutation_kinds: Vec<u8> = (0..=11).collect();

    // Apply every mutation to example seeds
    for seed_vec in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(seed_vec.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Hand-crafted seeds for boundary/diversity coverage
    let crafted: Vec<Vec<i32>> = vec![
        vec![1],
        vec![-1],
        vec![10, -10],
        vec![5, -5, 5, -5],
        vec![1, -1, 1, -1, 1, -1],
        vec![10, 10, 10, 10],
        vec![-10, -10, -10, -10],
        vec![1, 2, 3, -6],
        vec![1, -1],
    ];

    for seed_vec in &crafted {
        for &mk in &mutation_kinds {
            let result = mutate(seed_vec.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 100),
            _ => rng.gen_range_usize(1, 100),
        };
        let seed_vec = random_nonzero_vec(&mut rng, n);
        let mk = rng.gen_range_usize(0, 11) as u8;
        let result = mutate(seed_vec, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
