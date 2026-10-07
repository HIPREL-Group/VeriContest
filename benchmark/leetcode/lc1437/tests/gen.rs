use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 100000,
        0 <= k <= nums.len(),
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1,
    ensures
        1 <= result.0.len() <= 100000,
        0 <= result.1 <= result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1,
{
    if mutation_kind == 0 {
        // identity
        (nums, k)
    } else if mutation_kind == 1 {
        // set all elements to 0
        let n = nums.len();
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                1 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> #[trigger] d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> 0 <= #[trigger] d[j] <= 1,
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 2 {
        // set all elements to 1
        let n = nums.len();
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                1 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> #[trigger] d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> 0 <= #[trigger] d[j] <= 1,
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 3 {
        // flip last element
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] == 0 {
            d.set(last, 1);
        } else {
            d.set(last, 0);
        }
        (d, k)
    } else if mutation_kind == 4 {
        // flip first element
        let mut d = nums;
        if d[0] == 0 {
            d.set(0, 1);
        } else {
            d.set(0, 0);
        }
        (d, k)
    } else if mutation_kind == 5 {
        // k = 0 (any binary array is trivially valid)
        (nums, 0i32)
    } else if mutation_kind == 6 {
        // k = len (maximum valid k)
        let n = nums.len() as i32;
        (nums, n)
    } else if mutation_kind == 7 && nums.len() < 100000 {
        // grow by one (push 0)
        let mut d = nums;
        d.push(0);
        (d, k)
    } else if mutation_kind == 8 && nums.len() > 1 {
        // shrink by one (pop), reset k to 0 to guarantee constraint
        let mut d = nums;
        d.pop();
        (d, 0i32)
    } else {
        // fallback: identity
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

fn random_binary_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 1) as i32);
    }
    v
}

fn mutate(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(nums, k, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1437);
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
        let key = format!("{:?}|{}", nums, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::k_length_apart(nums.clone(), k);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "k": k},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    emit(vec![1,0,0,0,1,0,0,1], 2, &mut seen, &mut out, &mut count);
    emit(vec![1,0,0,1,0,1], 2, &mut seen, &mut out, &mut count);

    // Curated seeds covering boundary and interesting cases
    let seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![0], 0),
        (vec![1], 0),
        (vec![1], 1),
        (vec![0, 0, 0], 0),
        (vec![1, 1], 0),
        (vec![1, 0, 1], 1),
        (vec![1, 0, 1], 2),
        (vec![1, 0, 0, 1], 2),
        (vec![1, 0, 0, 0, 1], 3),
        (vec![0, 1, 0, 0, 0, 1, 0], 3),
        (vec![1, 0, 0, 0, 0, 1], 4),
        (vec![1, 0, 0, 0, 0, 1], 5),
        (vec![0, 0, 0, 0, 0], 3),
        (vec![1, 1, 1, 1, 1], 0),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    // Apply every mutation to every seed
    for (nums, k) in &seeds {
        for &mk in &mutation_kinds {
            let (result_nums, result_k) = mutate(nums.clone(), *k, mk);
            emit(result_nums, result_k, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // very large
        };
        let nums = random_binary_array(&mut rng, n);
        let k = rng.gen_range_i64(0, n as i64) as i32;
        let mk = rng.gen_range_usize(0, 8) as u8;
        let (result_nums, result_k) = mutate(nums, k, mk);
        emit(result_nums, result_k, &mut seen, &mut out, &mut count);
    }
}
