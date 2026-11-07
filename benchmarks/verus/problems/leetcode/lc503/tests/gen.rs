use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 10_000,
        forall|i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] != -1i32,
    ensures
        1 <= result.len() <= 10_000,
        forall|i: int| 0 <= i < result.len() ==> -1_000_000_000 <= #[trigger] result[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] != -1i32,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 2 {
        // set last element to max boundary (1_000_000_000)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1_000_000_000);
        d
    } else if mutation_kind == 3 {
        // set all elements to the same value (0)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 10_000,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && nums.len() < 10_000 {
        // grow by one element (push 0)
        let mut d = nums;
        d.push(0);
        d
    } else if mutation_kind == 5 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 6 {
        // set first element to min boundary (-1_000_000_000)
        let mut d = nums;
        d.set(0, -1_000_000_000);
        d
    } else if mutation_kind == 7 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let tmp_first = d[0];
        let tmp_last = d[last];
        d.set(0, tmp_last);
        d.set(last, tmp_first);
        d
    } else if mutation_kind == 8 {
        // nudge last element: if < 1_000_000_000 and != -2, increment by 1
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 1_000_000_000 && d[last] != -2i32 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 9 {
        // set all elements to 1_000_000_000
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 10_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1_000_000_000i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1_000_000_000);
            i += 1;
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
        loop {
            let v = rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32;
            if v != -1 {
                nums.push(v);
                break;
            }
        }
    }
    nums
}

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(503);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let key = format!("{:?}", nums);
        if seen.contains(&key) { return; }
        seen.insert(key);
        let result = Solution::next_greater_elements(nums.clone());
        writeln!(out, "{}", json!({
            "input": { "nums": nums },
            "output": result
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![1, 2, 1], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 3, 4, 3], &mut seen, &mut out, &mut count);

    // Boundary / special cases
    emit(vec![0], &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![-1_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![0, 0], &mut seen, &mut out, &mut count);
    emit(vec![5, 4, 3, 2, 1], &mut seen, &mut out, &mut count);  // strictly decreasing
    emit(vec![1, 2, 3, 4, 5], &mut seen, &mut out, &mut count);  // strictly increasing
    emit(vec![3, 3, 3, 3], &mut seen, &mut out, &mut count);     // all same

    // Size classes × mutation kinds
    let size_classes: Vec<usize> = vec![1, 2, 3, 5, 10, 50, 100, 500, 1000, 5000, 10000];
    let num_mutations: u8 = 10;

    for &sz in &size_classes {
        if count >= count_target { break; }
        let base = random_nums(&mut rng, sz);
        for mk in 0..num_mutations {
            if count >= count_target { break; }
            let mutated = mutate(base.clone(), mk);
            emit(mutated, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random inputs and random mutations
    while count < count_target {
        let sz = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let base = random_nums(&mut rng, sz);
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let mutated = mutate(base, mk);
        emit(mutated, &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} test cases", count);
}
