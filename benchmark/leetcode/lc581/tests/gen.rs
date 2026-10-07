use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 10_000,
        forall|i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
    ensures
        1 <= result.len() <= 10_000,
        forall|i: int| 0 <= i < result.len() ==> -100_000 <= #[trigger] result[i] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to min boundary
        let mut d = nums;
        d.set(0, -100_000);
        d
    } else if mutation_kind == 2 {
        // set last element to max boundary
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 100_000);
        d
    } else if mutation_kind == 3 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
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
        // set all elements to 0
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
    } else if mutation_kind == 7 {
        // set first element to 0
        let mut d = nums;
        d.set(0, 0);
        d
    } else if mutation_kind == 8 && nums.len() >= 2 {
        // nudge second element: if < 100_000, increment
        let mut d = nums;
        if d[1] < 100_000 {
            d.set(1, d[1] + 1);
        }
        d
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // set second element equal to first (create duplicate)
        let mut d = nums;
        let v = d[0];
        d.set(1, v);
        d
    } else {
        nums // fallback
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

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(-100_000, 100_000) as i32);
    }
    nums
}

fn sorted_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = random_array(rng, len);
    nums.sort();
    nums
}

fn nearly_sorted_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = sorted_array(rng, len);
    if len >= 2 {
        let i = rng.gen_range_usize(0, len - 2);
        let j = rng.gen_range_usize(i + 1, len - 1);
        nums.swap(i, j);
    }
    nums
}

fn reverse_sorted_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = sorted_array(rng, len);
    nums.reverse();
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(581);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::find_unsorted_subarray(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 6, 4, 8, 10, 9, 15],
        vec![1, 2, 3, 4],
        vec![1],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut emitted);
    }

    // Hand-crafted seed arrays covering interesting structures
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 2, 3, 4, 5],                     // fully sorted
        vec![5, 4, 3, 2, 1],                     // fully reversed
        vec![1, 3, 2, 4, 5],                     // one swap in middle
        vec![2, 1],                               // minimal unsorted
        vec![1, 2],                               // minimal sorted
        vec![-100_000, 0, 100_000],               // boundary values
        vec![1, 1, 1, 1],                         // all same
        vec![1, 2, 3, 5, 4],                      // unsorted at end
        vec![2, 1, 3, 4, 5],                      // unsorted at start
        vec![1, 5, 3, 4, 2, 6],                   // unsorted middle
        vec![0],                                   // single zero
        vec![-1, -2, -3],                          // negative reversed
        vec![-3, -2, -1],                          // negative sorted
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            emit(mutate(s.clone(), mk), &mut seen, &mut out, &mut emitted);
        }
    }

    // Generate diverse random arrays with mutations
    for i in 0..80 {
        if emitted >= count { break; }
        let len = match i % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 10000),// max
        };
        let arr = match i % 4 {
            0 => random_array(&mut rng, len),
            1 => sorted_array(&mut rng, len),
            2 => nearly_sorted_array(&mut rng, len),
            _ => reverse_sorted_array(&mut rng, len),
        };
        let mk = rng.gen_range_usize(0, 9) as u8;
        emit(mutate(arr, mk), &mut seen, &mut out, &mut emitted);
    }

    // Fill remaining with random arrays, identity mutation
    while emitted < count {
        let len = rng.gen_range_usize(1, 10000);
        let arr = random_array(&mut rng, len);
        emit(mutate(arr, 0), &mut seen, &mut out, &mut emitted);
    }
}
