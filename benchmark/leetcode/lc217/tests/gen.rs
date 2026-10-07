use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 10_000,
        forall|i: int| 1 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 10_000,
        forall|i: int| 1 <= i < result.len() ==> -1_000_000_000 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        nums
    } else if mutation_kind == 1 && nums.len() >= 2 {
        // force duplicate: set last element = element at index 1
        let mut d = nums;
        let last = d.len() - 1;
        let val = d[1];
        d.set(last, val);
        assert forall|i: int| 1 <= i < d.len() implies -1_000_000_000 <= #[trigger] d[i] <= 1_000_000_000 by {
            if i == last as int {
            }
        }
        d
    } else if mutation_kind == 2 && nums.len() >= 3 {
        // swap elements at index 1 and last (both in constrained range)
        let mut d = nums;
        let last = d.len() - 1;
        let tmp1 = d[1];
        let tmp_last = d[last];
        d.set(1, tmp_last);
        d.set(last, tmp1);
        assert forall|i: int| 1 <= i < d.len() implies -1_000_000_000 <= #[trigger] d[i] <= 1_000_000_000 by {
            if i == 1 {
            } else if i == last as int {
            }
        }
        d
    } else if mutation_kind == 3 && nums.len() < 10_000 {
        // grow: push element 0
        let mut d = nums;
        d.push(0i32);
        assert forall|i: int| 1 <= i < d.len() implies -1_000_000_000 <= #[trigger] d[i] <= 1_000_000_000 by {
            if i == (d.len() - 1) as int {
            }
        }
        d
    } else if mutation_kind == 4 && nums.len() > 1 {
        // shrink: pop last element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 5 {
        // set all elements (from index 1) to 42
        let mut d = nums;
        let mut i: usize = 1;
        while i < d.len()
            invariant
                1 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 10_000,
                forall|j: int| 1 <= j < i ==> d[j] == 42,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 42i32);
            i += 1;
        }
        assert forall|i: int| 1 <= i < d.len() implies -1_000_000_000 <= #[trigger] d[i] <= 1_000_000_000 by {
        }
        d
    } else if mutation_kind == 6 && nums.len() >= 2 {
        // nudge element at index 1 up
        let mut d = nums;
        if d[1] < 1_000_000_000 {
            d.set(1, d[1] + 1);
        }
        assert forall|i: int| 1 <= i < d.len() implies -1_000_000_000 <= #[trigger] d[i] <= 1_000_000_000 by {}
        d
    } else if mutation_kind == 7 && nums.len() >= 2 {
        // nudge element at index 1 down
        let mut d = nums;
        if d[1] > -1_000_000_000 {
            d.set(1, d[1] - 1);
        }
        assert forall|i: int| 1 <= i < d.len() implies -1_000_000_000 <= #[trigger] d[i] <= 1_000_000_000 by {}
        d
    } else if mutation_kind == 8 {
        // set element at index 1 to boundary min
        let mut d = nums;
        if d.len() >= 2 {
            d.set(1, -1_000_000_000i32);
        }
        assert forall|i: int| 1 <= i < d.len() implies -1_000_000_000 <= #[trigger] d[i] <= 1_000_000_000 by {}
        d
    } else if mutation_kind == 9 {
        // set element at index 1 to boundary max
        let mut d = nums;
        if d.len() >= 2 {
            d.set(1, 1_000_000_000i32);
        }
        assert forall|i: int| 1 <= i < d.len() implies -1_000_000_000 <= #[trigger] d[i] <= 1_000_000_000 by {}
        d
    } else {
        nums
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32);
    }
    nums
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

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::contains_duplicate(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3, 1],
        vec![1, 2, 3, 4],
        vec![1, 1, 1, 3, 3, 4, 3, 2, 4, 2],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Seed arrays with specific patterns
    let pattern_seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![0, 0],
        vec![0, 1],
        vec![0, 1_000_000_000],
        vec![0, -1_000_000_000],
        vec![0, 1_000_000_000, -1_000_000_000],
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    for seed_arr in &pattern_seeds {
        for mk in &mutation_kinds {
            let result = generate_test_case(seed_arr.clone(), *mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Diverse size classes with random mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 5),
        (6, 20),
        (21, 100),
        (101, 1000),
        (1001, 10000),
    ];
    for (lo, hi) in &size_classes {
        for _ in 0..10 {
            let len = rng.gen_range_usize(*lo, *hi);
            let nums = random_nums(&mut rng, len);
            let mk = rng.gen_range_usize(0, 9) as u8;
            let result = generate_test_case(nums, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random arrays
    while count < target_count {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 1000),
            _ => rng.gen_range_usize(1000, 10000),
        };
        let nums = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = generate_test_case(nums, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
