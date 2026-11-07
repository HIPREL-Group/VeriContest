use vstd::prelude::*;

verus! {

pub fn generate_test_case(base: Vec<i32>, zero_pos: usize, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= base.len() <= 100,
        forall|i: int| 0 <= i < base.len() ==> #[trigger] base[i] >= 0,
        forall|i: int| 0 <= i < base.len() ==> #[trigger] base[i] <= 100,
        0 <= zero_pos < base.len(),
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] >= 0,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] <= 100,
        exists|i: int| 0 <= i < result.len() && result[i] == 0,
{
    // Place a zero at zero_pos
    let mut nums = base;
    nums.set(zero_pos, 0);

    if mutation_kind == 0 {
        // identity
        assert(nums[zero_pos as int] == 0);
        nums
    } else if mutation_kind == 1 {
        // set all elements to 0
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() == base.len(),
                1 <= nums.len() <= 100,
                forall|j: int| 0 <= j < i ==> #[trigger] nums[j] == 0,
                forall|j: int| i <= j < nums.len() ==> #[trigger] nums[j] >= 0,
                forall|j: int| i <= j < nums.len() ==> #[trigger] nums[j] <= 100,
            decreases nums.len() - i,
        {
            nums.set(i, 0);
            i += 1;
        }
        assert(nums[0] == 0);
        nums
    } else if mutation_kind == 2 && nums.len() < 100 {
        // grow by one element (push 0)
        nums.push(0);
        let ghost last_idx = (nums.len() - 1) as int;
        assert(nums[last_idx] == 0);
        nums
    } else if mutation_kind == 3 && nums.len() > 1 && zero_pos < nums.len() - 1 {
        // shrink by one (pop last element), zero_pos is still valid
        nums.pop();
        assert(nums[zero_pos as int] == 0);
        nums
    } else if mutation_kind == 4 {
        // set element at index 0 to 100 (max boundary), unless zero_pos == 0
        if zero_pos != 0 {
            nums.set(0, 100);
        }
        assert(nums[zero_pos as int] == 0);
        nums
    } else if mutation_kind == 5 {
        // nudge element at last position: if nonzero and < 100, increment
        let last = nums.len() - 1;
        if last != zero_pos && nums[last] < 100 {
            nums.set(last, nums[last] + 1);
        }
        assert(nums[zero_pos as int] == 0);
        nums
    } else if mutation_kind == 6 {
        // nudge element at last position down: if > 0, decrement
        let last = nums.len() - 1;
        if last != zero_pos && nums[last] > 0 {
            nums.set(last, nums[last] - 1);
        }
        assert(nums[zero_pos as int] == 0);
        nums
    } else if mutation_kind == 7 && nums.len() >= 2 {
        // swap first and last elements
        let last = nums.len() - 1;
        let tmp_first = nums[0];
        let tmp_last = nums[last];
        nums.set(0, tmp_last);
        nums.set(last, tmp_first);
        // zero_pos was set to 0 earlier; after swap it could be at 0 or last
        if zero_pos == 0 {
            assert(nums[last as int] == 0);
        } else if zero_pos == last {
            assert(nums[0] == 0);
        } else {
            assert(nums[zero_pos as int] == 0);
        }
        nums
    } else {
        // fallback: identity
        assert(nums[zero_pos as int] == 0);
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

fn mutate(base: Vec<i32>, zero_pos: usize, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(base, zero_pos, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 100) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3354);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::count_valid_selections(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 0, 2, 0, 3],
        vec![2, 3, 4, 0, 4, 1, 0],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seeds
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![0, 0],
        vec![0, 0, 0],
        vec![1, 0, 1],
        vec![0, 1],
        vec![1, 0],
        vec![5, 0, 5],
        vec![100, 0, 100],
        vec![0, 100],
        vec![100, 0],
        vec![50, 50, 0, 50, 50],
        vec![1, 2, 3, 0, 6],
        vec![3, 0, 1, 2],
        vec![0, 0, 0, 0, 0],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Apply every mutation to every seed
    for seed_arr in &seeds {
        for &mk in &mutation_kinds {
            if count >= target_count { break; }
            let zero_pos = seed_arr.iter().position(|&x| x == 0).unwrap_or(0);
            let result = mutate(seed_arr.clone(), zero_pos, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random arrays with random mutations, diverse sizes
    while count < target_count {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 100),
            _ => rng.gen_range_usize(1, 100),
        };
        let mut base = random_array(&mut rng, len);
        let zero_pos = rng.gen_range_usize(0, len - 1);
        base[zero_pos] = 0; // ensure valid construction param
        let mk = rng.gen_range_usize(0, 7) as u8;
        let result = mutate(base, zero_pos, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
