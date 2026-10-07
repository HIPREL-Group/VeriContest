use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>, len: usize, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= len <= 1000,
        values.len() >= len,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000,
{
    // Slice values down to the requested length
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            nums.len() == i,
            len <= values.len(),
            1 <= len <= 1000,
            forall|j: int| 0 <= j < i ==> #[trigger] nums[j] == values[j],
            forall|j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 1000,
            forall|j: int| 0 <= j < i ==> 1 <= #[trigger] nums[j] <= 1000,
        decreases len - i,
    {
        nums.push(values[i]);
        i += 1;
    }

    if mutation_kind == 1 && nums.len() > 1 {
        // Set first element to 1 (boundary low)
        let mut m = nums;
        m.set(0, 1);
        m
    } else if mutation_kind == 2 && nums.len() > 1 {
        // Set last element to 1000 (boundary high)
        let mut m = nums;
        let last = m.len() - 1;
        m.set(last, 1000);
        m
    } else if mutation_kind == 3 {
        // Set all elements to 1
        let mut m = nums;
        let mut j: usize = 0;
        while j < m.len()
            invariant
                0 <= j <= m.len(),
                m.len() == nums.len(),
                1 <= m.len() <= 1000,
                forall|k: int| 0 <= k < j ==> #[trigger] m[k] == 1i32,
                forall|k: int| j <= k < m.len() ==> #[trigger] m[k] == nums[k],
                forall|k: int| 0 <= k < j ==> 1 <= #[trigger] m[k] <= 1000,
                forall|k: int| j <= k < m.len() ==> 1 <= #[trigger] m[k] <= 1000,
            decreases m.len() - j,
        {
            m.set(j, 1);
            j += 1;
        }
        m
    } else if mutation_kind == 4 {
        // Set all elements to 1000
        let mut m = nums;
        let mut j: usize = 0;
        while j < m.len()
            invariant
                0 <= j <= m.len(),
                m.len() == nums.len(),
                1 <= m.len() <= 1000,
                forall|k: int| 0 <= k < j ==> #[trigger] m[k] == 1000i32,
                forall|k: int| j <= k < m.len() ==> #[trigger] m[k] == nums[k],
                forall|k: int| 0 <= k < j ==> 1 <= #[trigger] m[k] <= 1000,
                forall|k: int| j <= k < m.len() ==> 1 <= #[trigger] m[k] <= 1000,
            decreases m.len() - j,
        {
            m.set(j, 1000);
            j += 1;
        }
        m
    } else if mutation_kind == 5 && nums.len() > 1 {
        // Swap first and last elements
        let mut m = nums;
        let last = m.len() - 1;
        let first_val = m[0];
        let last_val = m[last];
        m.set(0, last_val);
        m.set(last, first_val);
        m
    } else if mutation_kind == 6 && nums.len() > 1 {
        // Pop last element (shrink by one)
        let mut m = nums;
        m.pop();
        m
    } else if mutation_kind == 7 && nums.len() < 1000 {
        // Push element 500 (grow by one)
        let mut m = nums;
        m.push(500);
        m
    } else if mutation_kind == 8 {
        // Nudge first element: if < 1000 increment, else set to 1
        let mut m = nums;
        if m[0] < 1000 {
            m.set(0, m[0] + 1);
        } else {
            m.set(0, 1);
        }
        m
    } else {
        // identity (mutation_kind == 0 or fallback)
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

extern crate serde_json;
use serde_json::json;

fn random_values(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 1000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1929);
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
        let output = Solution::get_concatenation(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from the problem description
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![1, 2, 1],
        vec![1, 3, 2, 1],
    ];

    // Hand-crafted boundary seeds
    let boundary_seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1000],
        vec![1, 1000],
        vec![500, 500, 500],
        vec![1, 2, 3, 4, 5],
        vec![1000, 999, 998],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    // Apply every mutation to example seeds
    for seed in &example_seeds {
        for &mk in &mutation_kinds {
            let result = generate_test_case(seed.clone(), seed.len(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Apply every mutation to boundary seeds
    for seed in &boundary_seeds {
        for &mk in &mutation_kinds {
            let result = generate_test_case(seed.clone(), seed.len(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 500),    // large
            _ => rng.gen_range_usize(501, 1000),   // max
        };
        let values = random_values(&mut rng, n);
        let mk = rng.gen_range_usize(0, 8) as u8;
        let result = generate_test_case(values, n, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} test cases", count);
}
