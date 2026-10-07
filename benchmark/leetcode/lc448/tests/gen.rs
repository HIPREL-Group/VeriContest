use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        nums.len() >= 1,
        nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= nums.len(),
    ensures
        result.len() >= 1,
        result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= result.len(),
{
    let n = nums.len();

    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to 1
        let mut d = nums;
        d.set(0, 1);
        d
    } else if mutation_kind == 2 {
        // set first element to n
        let mut d = nums;
        d.set(0, n as i32);
        d
    } else if mutation_kind == 3 {
        // set all elements to 1 (maximizes disappeared numbers)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                n >= 1,
                n <= 100_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set all elements to n (only value n present)
        let mut d = nums;
        let len = d.len();
        let val = len as i32;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                n >= 1,
                n <= 100_000,
                val == n as i32,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 5 {
        // set last element to 1
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 6 {
        // set last element to n
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, n as i32);
        d
    } else if mutation_kind == 7 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        d
    } else if mutation_kind == 8 && nums.len() < 100_000 {
        // grow: push element 1 (new length = n+1, all old elements <= n < n+1)
        let mut d = nums;
        d.push(1);
        assert(d.len() == n + 1);
        assert(forall|i: int| 0 <= i < n ==> d[i] == nums[i]);
        assert(d[n as int] == 1i32);
        assert(forall|i: int| 0 <= i < n ==> 1 <= #[trigger] d[i] <= n);
        assert(forall|i: int| 0 <= i < n ==> #[trigger] d[i] <= (n + 1) as i32);
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

fn random_nums(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i64(1, n as i64) as i32);
    }
    v
}

fn make_permutation(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (1..=n as i32).collect();
    // Fisher-Yates shuffle
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
    }
    v
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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(448);
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
        let output = Solution::find_disappeared_numbers(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![4, 3, 2, 7, 8, 2, 3, 1],
        vec![1, 1],
    ];
    for ex in &examples {
        for mk in 0..=8u8 {
            emit(mutate(ex.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Interesting seed arrays
    let hand_seeds: Vec<Vec<i32>> = vec![
        vec![1],                           // single element, nothing disappears
        vec![1, 2, 3, 4, 5],              // permutation, nothing disappears
        vec![1, 1, 1, 1, 1],              // all same
        vec![5, 5, 5, 5, 5],              // all same at max
        vec![3, 3, 3],                     // all same, middle value
        vec![1, 2, 1, 2],                 // two distinct values
        vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1], // 10 ones
    ];
    for s in &hand_seeds {
        for mk in 0..=8u8 {
            emit(mutate(s.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Permutations (no disappeared numbers)
    for &n in &[2usize, 5, 10, 50, 100] {
        let perm = make_permutation(&mut rng, n);
        for mk in 0..=8u8 {
            emit(mutate(perm.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Random arrays with diverse sizes
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];
    for i in 0..80 {
        if count >= target_count { break; }
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10_000), // very large
        };
        let nums = random_nums(&mut rng, n);
        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        emit(mutate(nums, mk), &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random arrays, identity mutation
    while count < target_count {
        let n = rng.gen_range_usize(1, 10_000);
        let nums = random_nums(&mut rng, n);
        emit(mutate(nums, 0), &mut seen, &mut out, &mut count);
    }
}
