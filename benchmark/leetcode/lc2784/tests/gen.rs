use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 200,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 200,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 2 {
        // set last element to 200 (max boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 200);
        d
    } else if mutation_kind == 3 {
        // set all elements to the same value
        let mut d = nums;
        let val = d[0];
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                1 <= val <= 200,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && nums.len() < 100 {
        // grow by one element (push element value 1)
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 5 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 6 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let tmp = d[0];
        d.set(0, d[last]);
        d.set(last, tmp);
        d
    } else if mutation_kind == 7 {
        // nudge first element: if < 200, increment by 1
        let mut d = nums;
        if d[0] < 200 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 8 {
        // nudge first element down: if > 1, decrement by 1
        let mut d = nums;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 9 {
        // set first element to middle value 100
        let mut d = nums;
        d.set(0, 100);
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

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 200) as i32);
    }
    nums
}

/// Build a "good" array: base[n] = [1, 2, ..., n-1, n, n] (shuffled)
fn make_good_array(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(n + 1);
    for i in 1..n {
        nums.push(i as i32);
    }
    nums.push(n as i32);
    nums.push(n as i32);
    // Fisher-Yates shuffle
    let len = nums.len();
    for i in (1..len).rev() {
        let j = rng.gen_range_usize(0, i);
        nums.swap(i, j);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2784);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::is_good(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 1, 3],
        vec![1, 3, 3, 2],
        vec![1, 1],
        vec![3, 4, 4, 1, 2, 1],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Manually crafted seeds: good arrays
    for n in 1..=10 {
        let good = make_good_array(&mut rng, n);
        emit(good, &mut seen, &mut out, &mut count);
    }

    // Manually crafted: near-good arrays (off by one element)
    for n in 2..=8 {
        let mut bad = make_good_array(&mut rng, n);
        // replace one n with n-1 to break "good" property
        for i in 0..bad.len() {
            if bad[i] == n as i32 {
                bad[i] = (n - 1) as i32;
                break;
            }
        }
        emit(bad, &mut seen, &mut out, &mut count);
    }

    // Edge cases
    emit(vec![1], &mut seen, &mut out, &mut count);                    // length 1
    emit(vec![200], &mut seen, &mut out, &mut count);                  // single max value
    emit(vec![1, 2], &mut seen, &mut out, &mut count);                 // not good: n=1, needs [1,1]
    emit(vec![2, 2], &mut seen, &mut out, &mut count);                 // not good: missing 1

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Good arrays + mutations
    for n in &[1, 2, 3, 5, 10, 20, 50, 99] {
        let good = make_good_array(&mut rng, *n);
        for &mk in &mutation_kinds {
            let result = mutate(good.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random arrays with random mutations across size classes
    while count < count_target {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 50),     // medium
            3 => rng.gen_range_usize(51, 100),    // large
            _ => rng.gen_range_usize(1, 100),     // fallback
        };
        let seed_arr = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(seed_arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
