use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: &mut Vec<i32>, val: i32, mutation_kind: u8)
    requires
        0 <= old(nums).len() <= 100,
        forall|i: int| 0 <= i < old(nums).len() ==>
            0 <= #[trigger] old(nums)[i] <= 50,
        0 <= val <= 100,
    ensures
        0 <= old(nums).len() <= 100,
        forall|i: int| 0 <= i < old(nums).len() ==>
            0 <= #[trigger] old(nums)[i] <= 50,
        0 <= val <= 100,
        0 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==>
            0 <= #[trigger] nums[i] <= 50,
{
    if mutation_kind == 0 {
        // identity
    } else if mutation_kind == 1 && nums.len() > 0 {
        let last = nums.len() - 1;
        nums.set(last, 0);
    } else if mutation_kind == 2 && nums.len() > 0 {
        let n = nums.len();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                nums.len() == n,
                0 <= n <= 100,
                forall|j: int| 0 <= j < k as int ==> #[trigger] nums[j] == 0,
                forall|j: int| k as int <= j < n as int ==> 0 <= #[trigger] nums[j] <= 50,
            decreases n - k,
        {
            nums.set(k, 0);
            k += 1;
        }
    } else if mutation_kind == 3 && nums.len() < 100 {
        nums.push(0);
    } else if mutation_kind == 4 && nums.len() > 0 {
        let ghost pre = nums@;
        let _ = nums.pop();
        proof {
            assert(nums@ =~= pre.subrange(0, pre.len() - 1));
            assert forall|i: int| 0 <= i < nums.len() implies
                0 <= #[trigger] nums[i] <= 50 by {
                assert(nums[i] == pre[i]);
            };
        }
    } else if mutation_kind == 5 && nums.len() > 0 {
        let n = nums.len();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                nums.len() == n,
                0 <= n <= 100,
                forall|j: int| 0 <= j < k as int ==> #[trigger] nums[j] == 50,
                forall|j: int| k as int <= j < n as int ==> 0 <= #[trigger] nums[j] <= 50,
            decreases n - k,
        {
            nums.set(k, 50);
            k += 1;
        }
    } else if mutation_kind == 6 && nums.len() > 0 {
        if nums[0] < 50 {
            nums.set(0, nums[0] + 1);
        }
    } else if mutation_kind == 7 && nums.len() > 0 {
        if nums[0] > 0 {
            nums.set(0, nums[0] - 1);
        }
    } else if mutation_kind == 8 && nums.len() >= 2 {
        let last = nums.len() - 1;
        let tmp = nums[0];
        nums.set(0, nums[last]);
        nums.set(last, tmp);
    } else {
        // fallback identity
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(0, 50) as i32);
    }
    nums
}

fn mutate(nums: &mut Vec<i32>, val: i32, mutation_kind: u8) {
    generate_test_case(nums, val, mutation_kind);
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, val: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}_{}", nums, val);
        if !seen.insert(key) {
            return;
        }
        let mut nums_clone = nums.clone();
        let k = Solution::remove_element(&mut nums_clone, val);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "val": val},
            "output": k
        })).unwrap();
        *count += 1;
    };

    // Example test cases from the problem description
    emit(vec![3, 2, 2, 3], 3, &mut seen, &mut out, &mut count);
    emit(vec![0, 1, 2, 2, 3, 0, 4, 2], 2, &mut seen, &mut out, &mut count);

    // Boundary: empty array
    emit(vec![], 0, &mut seen, &mut out, &mut count);
    emit(vec![], 50, &mut seen, &mut out, &mut count);
    emit(vec![], 100, &mut seen, &mut out, &mut count);

    // Single element cases
    for v in [0, 1, 25, 50] {
        emit(vec![v], v, &mut seen, &mut out, &mut count);
        emit(vec![v], v + 1, &mut seen, &mut out, &mut count);
    }

    // Curated seeds
    let seed_nums: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1],
        vec![50],
        vec![1, 1, 1],
        vec![0, 0, 0, 0],
        vec![1, 2, 3, 4, 5],
        vec![50, 50, 50],
        vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
        vec![25, 25, 25, 25, 25],
    ];
    let seed_vals: Vec<i32> = vec![0, 1, 2, 3, 25, 50, 51, 99, 100];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    for nums in &seed_nums {
        for &val in &seed_vals {
            for &mk in &mutation_kinds {
                if count >= target_count { break; }
                let mut nums_m = nums.clone();
                mutate(&mut nums_m, val, mk);
                emit(nums_m, val, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random seeds with random mutations across size classes
    while count < target_count {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(0, 3),
            1 => rng.gen_range_usize(0, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 100),
            _ => rng.gen_range_usize(0, 100),
        };
        let mut nums = random_nums(&mut rng, len);
        let val = if rng.gen_range_usize(0, 4) == 0 {
            *[0i32, 1, 50, 51, 100].get(rng.gen_range_usize(0, 4)).unwrap()
        } else {
            rng.gen_range_i64(0, 100) as i32
        };
        let mk = rng.gen_range_usize(0, 8) as u8;
        mutate(&mut nums, val, mk);
        emit(nums, val, &mut seen, &mut out, &mut count);
    }
}
