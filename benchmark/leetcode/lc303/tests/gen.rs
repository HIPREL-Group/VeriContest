use vstd::prelude::*;

verus! {

pub struct NumArray {
    pub prefix: Vec<i64>,
}

impl NumArray {
    pub fn generate_test_case(
        &self,
        left: i32,
        right_raw: i32,
        mutation_kind: u8,
    ) -> (right: i32)
        requires
            self.prefix@.len() >= 2,
            self.prefix@.len() <= 10001,
            0 <= left <= right_raw < (self.prefix@.len() - 1) as int,
            forall|i: int| 0 <= i < self.prefix@.len() ==>
                -1_000_000_000 <= (#[trigger] self.prefix@[i]) <= 1_000_000_000,
        ensures
            self.prefix@.len() >= 1,
            0 <= left <= right < (self.prefix@.len() - 1) as int,
            forall|i: int| 0 <= i < self.prefix@.len() ==>
                -1_000_000_000 <= (#[trigger] self.prefix@[i]) <= 1_000_000_000,
    {
        let last_idx = (self.prefix.len() - 2) as i32;

        if mutation_kind == 0 {
            // identity
            right_raw
        } else if mutation_kind == 1 {
            // query to end of array
            last_idx
        } else if mutation_kind == 2 {
            // single element query (left == right)
            left
        } else if mutation_kind == 3 && right_raw > left {
            // shrink range from right
            right_raw - 1
        } else if mutation_kind == 4 && right_raw < last_idx {
            // expand range right
            right_raw + 1
        } else if mutation_kind == 5 {
            // midpoint between left and right_raw
            left + (right_raw - left) / 2
        } else {
            // fallback
            right_raw
        }
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

fn build_num_array(nums: &[i32]) -> NumArray {
    let mut prefix = Vec::with_capacity(nums.len() + 1);
    prefix.push(0i64);
    for &v in nums {
        let last = *prefix.last().unwrap();
        prefix.push(last + v as i64);
    }
    NumArray { prefix }
}

fn compute_sum_range(prefix: &[i64], left: i32, right: i32) -> i32 {
    (prefix[right as usize + 1] - prefix[left as usize]) as i32
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(-100000, 100000) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(303);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: &[i32], left: i32, right: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}_{}_{}",  nums, left, right);
        if !seen.insert(key) {
            return;
        }
        let na = build_num_array(nums);
        let output = compute_sum_range(&na.prefix, left, right);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "left": left, "right": right},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example from description.md
    let example_nums: Vec<i32> = vec![-2, 0, 3, -5, 2, -1];
    for &(l, r) in &[(0i32, 2i32), (2, 5), (0, 5)] {
        emit(&example_nums, l, r, &mut seen, &mut out, &mut count);
    }

    // Seed arrays with diverse characteristics
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![0],
        vec![100000],
        vec![-100000],
        vec![1, 2, 3, 4, 5],
        vec![-1, -2, -3, -4, -5],
        vec![0, 0, 0, 0, 0],
        vec![100000, -100000, 100000, -100000],
        vec![1],
        vec![42, -17, 0, 99, -100000, 100000, 3, -3],
    ];

    let mutation_kinds: Vec<u8> = (0..=5).collect();

    // Apply every mutation to every seed array with varied index positions
    for seed_arr in &seed_arrays {
        let na = build_num_array(seed_arr);
        let n = seed_arr.len();
        for &mk in &mutation_kinds {
            // left=0, right_raw=last index
            let left = 0i32;
            let right_raw = (n - 1) as i32;
            let right = na.generate_test_case(left, right_raw, mk);
            emit(seed_arr, left, right, &mut seen, &mut out, &mut count);

            // left=mid, right_raw=last index
            if n > 1 {
                let mid = (n / 2) as i32;
                let right2 = na.generate_test_case(mid, right_raw, mk);
                emit(seed_arr, mid, right2, &mut seen, &mut out, &mut count);
            }

            // left=0, right_raw=mid
            if n > 2 {
                let mid = (n / 2) as i32;
                let right3 = na.generate_test_case(0, mid, mk);
                emit(seed_arr, 0, right3, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random test cases with diverse size classes
    while count < target_count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10000),  // max
        };

        let nums = random_nums(&mut rng, n);
        let na = build_num_array(&nums);
        let left = rng.gen_range_usize(0, n - 1) as i32;
        let right_raw = rng.gen_range_usize(left as usize, n - 1) as i32;
        let mk = rng.gen_range_usize(0, 5) as u8;

        let right = na.generate_test_case(left, right_raw, mk);
        emit(&nums, left, right, &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} test cases", count);
}
