use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums: Vec<i32>,
    limit: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 100_000,
        0 <= limit <= 1_000_000_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        0 <= result.1 <= 1_000_000_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        (nums, limit)
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut n = nums;
        n.set(0, 1);
        (n, limit)
    } else if mutation_kind == 2 {
        // set first element to 1_000_000_000 (max boundary)
        let mut n = nums;
        n.set(0, 1_000_000_000);
        (n, limit)
    } else if mutation_kind == 3 {
        // set limit to 0
        (nums, 0i32)
    } else if mutation_kind == 4 {
        // set limit to 1_000_000_000 (max)
        (nums, 1_000_000_000i32)
    } else if mutation_kind == 5 {
        // set all elements to 1
        let mut n = nums;
        let mut i: usize = 0;
        while i < n.len()
            invariant
                0 <= i <= n.len(),
                n.len() == nums.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] n[j] == 1i32,
                forall|j: int| i <= j < n.len() ==> n[j] == nums[j],
            decreases n.len() - i,
        {
            n.set(i, 1);
            i += 1;
        }
        (n, limit)
    } else if mutation_kind == 6 {
        // set all elements to 1_000_000_000
        let mut n = nums;
        let mut i: usize = 0;
        while i < n.len()
            invariant
                0 <= i <= n.len(),
                n.len() == nums.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] n[j] == 1_000_000_000i32,
                forall|j: int| i <= j < n.len() ==> n[j] == nums[j],
            decreases n.len() - i,
        {
            n.set(i, 1_000_000_000);
            i += 1;
        }
        (n, limit)
    } else if mutation_kind == 7 {
        // nudge first element up (if possible)
        let mut n = nums;
        if n[0] < 1_000_000_000 {
            n.set(0, n[0] + 1);
        }
        (n, limit)
    } else if mutation_kind == 8 {
        // nudge first element down (if possible)
        let mut n = nums;
        if n[0] > 1 {
            n.set(0, n[0] - 1);
        }
        (n, limit)
    } else if mutation_kind == 9 {
        // set last element to 1
        let mut n = nums;
        let last = n.len() - 1;
        n.set(last, 1);
        (n, limit)
    } else if mutation_kind == 10 {
        // set last element to 1_000_000_000
        let mut n = nums;
        let last = n.len() - 1;
        n.set(last, 1_000_000_000);
        (n, limit)
    } else if mutation_kind == 11 && nums.len() > 1 {
        // shrink: remove last element
        let mut n = nums;
        let ghost old_n = n@;
        n.pop();
        proof {
            assert forall|i: int| 0 <= i < n.len() implies 1 <= #[trigger] n[i] <= 1_000_000_000 by {
                assert(n[i] == old_n[i]);
            }
        }
        (n, limit)
    } else if mutation_kind == 12 && nums.len() < 100_000 {
        // grow: push element 1
        let mut n = nums;
        n.push(1);
        (n, limit)
    } else {
        // fallback: identity
        (nums, limit)
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

fn mutate(nums: Vec<i32>, limit: i32, mk: u8) -> (Vec<i32>, i32) {
    generate_test_case(nums, limit, mk)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1438);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, limit: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}|{}", nums, limit);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::longest_subarray(nums.clone(), limit);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "limit": limit},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description
    {
        let (n, l) = mutate(vec![8, 2, 4, 7], 4, 0);
        emit(n, l, &mut seen, &mut out, &mut count);
    }
    {
        let (n, l) = mutate(vec![10, 1, 2, 4, 7, 2], 5, 0);
        emit(n, l, &mut seen, &mut out, &mut count);
    }
    {
        let (n, l) = mutate(vec![4, 2, 2, 2, 4, 4, 2, 2], 0, 0);
        emit(n, l, &mut seen, &mut out, &mut count);
    }

    // Seed inputs × mutations
    let seed_inputs: Vec<(Vec<i32>, i32)> = vec![
        (vec![8, 2, 4, 7], 4),
        (vec![10, 1, 2, 4, 7, 2], 5),
        (vec![4, 2, 2, 2, 4, 4, 2, 2], 0),
        (vec![1], 0),
        (vec![1, 1_000_000_000], 999_999_999),
        (vec![1, 2, 3, 4, 5], 1_000_000_000),
        (vec![100, 200, 300], 50),
        (vec![5, 5, 5, 5], 0),
        (vec![1, 1_000_000_000, 1, 1_000_000_000], 0),
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];

    for (n, l) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (rn, rl) = mutate(n.clone(), *l, mk);
            emit(rn, rl, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases with diverse sizes
    while count < target_count {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 5000),  // very large
        };
        let limit = match count % 4 {
            0 => 0i32,
            1 => rng.gen_range_i64(1, 100) as i32,
            2 => rng.gen_range_i64(1, 1_000_000) as i32,
            _ => rng.gen_range_i64(0, 1_000_000_000) as i32,
        };
        let nums = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 12) as u8;
        let (rn, rl) = mutate(nums, limit, mk);
        emit(rn, rl, &mut seen, &mut out, &mut count);
    }
}
