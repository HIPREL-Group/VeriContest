use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < nums.len(),
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] < result.len(),
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
        // set all elements to 0
        let mut d = nums;
        let n = d.len();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                d.len() == n,
                1 <= n <= 100000,
                forall|j: int| 0 <= j < i as int ==> d[j] == 0i32,
                forall|j: int| i as int <= j < n as int ==> d[j] == nums[j],
            decreases n - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 3 && nums.len() < 100000 {
        // grow by one element (push 0)
        let mut d = nums;
        let old_len = d.len();
        d.push(0);
        assert(d.len() == old_len + 1);
        assert forall|i: int| 0 <= i < d.len() implies 0 <= #[trigger] d[i] < d.len() by {
            if i < old_len as int {
                assert(d[i] == nums[i]);
                assert(0 <= nums[i] < old_len as int);
                assert(d[i] < d.len());
            } else {
                assert(d[i] == 0i32);
            }
        }
        d
    } else if mutation_kind == 4 {
        // set last element to len - 1 (max valid value)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, (d.len() - 1) as i32);
        d
    } else if mutation_kind == 5 && nums.len() > 1 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        assert forall|i: int| 0 <= i < d.len() implies 0 <= #[trigger] d[i] < d.len() by {
            if i == 0 {
                assert(d[i] == last_val);
                assert(0 <= last_val < nums.len());
            } else if i == last as int {
                assert(d[i] == first_val);
                assert(0 <= first_val < nums.len());
            } else {
                assert(d[i] == nums[i]);
            }
        }
        d
    } else if mutation_kind == 6 {
        // nudge last element up if possible
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < (d.len() as i32 - 2) {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 7 {
        // nudge last element down if > 0
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 0 {
            d.set(last, d[last] - 1);
        }
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

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(0, len as i64 - 1) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2860);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::count_ways(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 1],
        vec![6, 0, 3, 3, 6, 7, 2, 7],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Emit examples with all mutations
    for ex in &examples {
        for &mk in &mutation_kinds {
            emit(mutate(ex.clone(), mk), &mut seen, &mut out, &mut emitted);
        }
    }

    // Hand-crafted seeds for diversity
    let hand_seeds: Vec<Vec<i32>> = vec![
        vec![0],                         // minimal length
        vec![0, 0],                      // all zeros
        vec![0, 0, 0],                   // all zeros length 3
        vec![2, 0, 1],                   // permutation of [0..n)
        vec![0, 1, 2, 3, 4],            // sorted ascending
        vec![4, 3, 2, 1, 0],            // sorted descending
        vec![0, 0, 0, 0, 0],            // all same
        vec![3, 3, 3, 3, 3, 3, 3],      // all same value < n
        vec![0, 1, 0, 1, 0],            // alternating
    ];

    for s in &hand_seeds {
        for &mk in &mutation_kinds {
            emit(mutate(s.clone(), mk), &mut seen, &mut out, &mut emitted);
        }
    }

    // Random inputs across size classes
    for i in 0..200 {
        if emitted >= count {
            break;
        }
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // very large
        };
        let nums = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 7) as u8;
        emit(mutate(nums, mk), &mut seen, &mut out, &mut emitted);
    }

    // Fill remaining with random inputs, identity mutation
    while emitted < count {
        let n = rng.gen_range_usize(1, 1000);
        let nums = random_nums(&mut rng, n);
        emit(mutate(nums, 0), &mut seen, &mut out, &mut emitted);
    }
}
