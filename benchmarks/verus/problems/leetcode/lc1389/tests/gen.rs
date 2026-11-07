use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums: Vec<i32>,
    index: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= nums.len() <= 100,
        nums.len() == index.len(),
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100,
        forall|i: int| 0 <= i < index.len() ==> 0 <= #[trigger] index[i] <= i,
    ensures
        1 <= result.0.len() <= 100,
        result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 100,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= i,
{
    if mutation_kind == 0 {
        // identity
        (nums, index)
    } else if mutation_kind == 1 && nums.len() > 1 {
        // swap first two elements in nums
        let mut n = nums;
        let tmp = n[0];
        n.set(0, n[1]);
        n.set(1, tmp);
        (n, index)
    } else if mutation_kind == 2 {
        // set first num to 0
        let mut n = nums;
        n.set(0, 0);
        (n, index)
    } else if mutation_kind == 3 {
        // set first num to 100
        let mut n = nums;
        n.set(0, 100);
        (n, index)
    } else if mutation_kind == 4 {
        // set all index entries to 0 (always valid since 0 <= 0 <= i)
        let mut idx = index;
        let mut i: usize = 0;
        while i < idx.len()
            invariant
                idx.len() == nums.len(),
                1 <= idx.len() <= 100,
                0 <= i <= idx.len(),
                forall|j: int| 0 <= j < i ==> idx[j] == 0i32,
                forall|j: int| i <= j < idx.len() ==> idx[j] == index[j],
            decreases idx.len() - i,
        {
            idx.set(i, 0);
            i = i + 1;
        }
        (nums, idx)
    } else if mutation_kind == 5 {
        // nudge first num up if < 100
        let mut n = nums;
        if n[0] < 100 {
            n.set(0, n[0] + 1);
        }
        (n, index)
    } else if mutation_kind == 6 {
        // nudge first num down if > 0
        let mut n = nums;
        if n[0] > 0 {
            n.set(0, n[0] - 1);
        }
        (n, index)
    } else if mutation_kind == 7 && nums.len() < 100 {
        // grow: append one element with num=0, index=len (last valid position)
        let mut n = nums;
        let mut idx = index;
        let new_idx = n.len() as i32;
        n.push(0);
        idx.push(new_idx);
        assert(forall|i: int| 0 <= i < n.len() - 1 ==> n[i] == nums[i]);
        assert(n[n.len() as int - 1] == 0i32);
        assert(forall|i: int| 0 <= i < idx.len() - 1 ==> idx[i] == index[i]);
        assert(idx[idx.len() as int - 1] == new_idx);
        (n, idx)
    } else if mutation_kind == 8 && nums.len() > 1 {
        // shrink: remove last element
        let mut n = nums;
        let mut idx = index;
        n.pop();
        idx.pop();
        (n, idx)
    } else if mutation_kind == 9 {
        // set all nums to 50
        let mut n = nums;
        let mut i: usize = 0;
        while i < n.len()
            invariant
                n.len() == nums.len(),
                1 <= n.len() <= 100,
                0 <= i <= n.len(),
                forall|j: int| 0 <= j < i ==> n[j] == 50i32,
                forall|j: int| i <= j < n.len() ==> n[j] == nums[j],
            decreases n.len() - i,
        {
            n.set(i, 50);
            i = i + 1;
        }
        (n, index)
    } else if mutation_kind == 10 {
        // set each index[i] = i (insert at end each time)
        let mut idx = index;
        let mut i: usize = 0;
        while i < idx.len()
            invariant
                idx.len() == nums.len(),
                1 <= idx.len() <= 100,
                0 <= i <= idx.len(),
                forall|j: int| 0 <= j < i ==> idx[j] == j as i32,
                forall|j: int| i <= j < idx.len() ==> idx[j] == index[j],
            decreases idx.len() - i,
        {
            idx.set(i, i as i32);
            i = i + 1;
        }
        (nums, idx)
    } else {
        // fallback: identity
        (nums, index)
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

fn mutate(nums: Vec<i32>, index: Vec<i32>, mutation_kind: u8) -> (Vec<i32>, Vec<i32>) {
    generate_test_case(nums, index, mutation_kind)
}

/// Generate a random valid (nums, index) pair of given length.
fn random_pair(rng: &mut Rng, len: usize) -> (Vec<i32>, Vec<i32>) {
    let mut nums = Vec::with_capacity(len);
    let mut index = Vec::with_capacity(len);
    for i in 0..len {
        nums.push(rng.gen_range_i64(0, 100) as i32);
        index.push(rng.gen_range_i64(0, i as i64) as i32);
    }
    (nums, index)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1389);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, index: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let key = format!("{:?},{:?}", nums, index);
        if *count >= target || !seen.insert(key) {
            return;
        }
        let output = Solution::create_target_array(nums.clone(), index.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums, "index": index}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let seeds: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![0, 1, 2, 3, 4], vec![0, 1, 2, 2, 1]),      // example 1
        (vec![1, 2, 3, 4, 0], vec![0, 1, 2, 3, 0]),      // example 2
        (vec![1], vec![0]),                                 // example 3 (minimal)
        (vec![0, 0], vec![0, 0]),                          // edge: all zeros
        (vec![100, 100], vec![0, 1]),                      // boundary: max values
        (vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), // all insert at 0
        (vec![50], vec![0]),                               // single element
        (vec![0, 100], vec![0, 0]),                        // insert at beginning
    ];

    let mutation_kinds: Vec<u8> = (0..=10).collect();

    // Apply every mutation to every seed
    for (n, idx) in &seeds {
        for &mk in &mutation_kinds {
            let (rn, ri) = mutate(n.clone(), idx.clone(), mk);
            emit(rn, ri, &mut seen, &mut out, &mut count);
        }
    }

    // Random pairs of various sizes
    for _ in 0..40 {
        let len = match rng.gen_range_usize(0, 4) {
            0 => 1,                                   // minimal
            1 => rng.gen_range_usize(2, 5),          // tiny
            2 => rng.gen_range_usize(6, 20),         // small
            3 => rng.gen_range_usize(21, 50),        // medium
            _ => rng.gen_range_usize(51, 100),       // max
        };
        let (nums, index) = random_pair(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let (rn, ri) = mutate(nums, index, mk);
        emit(rn, ri, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random pairs, identity mutation
    while count < target {
        let len = rng.gen_range_usize(1, 100);
        let (nums, index) = random_pair(&mut rng, len);
        let (rn, ri) = mutate(nums, index, 0);
        emit(rn, ri, &mut seen, &mut out, &mut count);
    }
}
