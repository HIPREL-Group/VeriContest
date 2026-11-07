use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: Vec<i32>, mutation_kind: u8) -> (nums: Vec<i32>)
    requires
        2 <= vals.len() <= 1000,
        forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1_000_000_000,
    ensures
        2 <= nums.len() <= 1000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        vals
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut v = vals;
        v.set(0, 1);
        v
    } else if mutation_kind == 2 {
        // set last element to max boundary
        let mut v = vals;
        let last = v.len() - 1;
        v.set(last, 1_000_000_000);
        v
    } else if mutation_kind == 3 {
        // set first to 1, last to max (maximize potential diff)
        let mut v = vals;
        v.set(0, 1);
        let last = v.len() - 1;
        v.set(last, 1_000_000_000);
        v
    } else if mutation_kind == 4 && vals.len() > 2 {
        // shrink: remove last element
        let mut v = vals;
        v.pop();
        v
    } else if mutation_kind == 5 && vals.len() < 1000 {
        // grow: push element 1
        let mut v = vals;
        v.push(1);
        v
    } else if mutation_kind == 6 {
        // set all elements to same value (ensures result == -1)
        let val = vals[0];
        let mut v = vals;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == vals.len(),
                2 <= v.len() <= 1000,
                forall|j: int| 0 <= j < i ==> v[j] == val,
                forall|j: int| i <= j < v.len() ==> v[j] == vals[j],
                1 <= val <= 1_000_000_000,
            decreases v.len() - i,
        {
            v.set(i, val);
            i += 1;
        }
        v
    } else if mutation_kind == 7 {
        // swap first two elements
        let mut v = vals;
        let tmp = v[0];
        v.set(0, v[1]);
        v.set(1, tmp);
        v
    } else if mutation_kind == 8 {
        // nudge first element: if > 1, decrement by 1
        let mut v = vals;
        if v[0] > 1 {
            v.set(0, v[0] - 1);
        }
        v
    } else if mutation_kind == 9 {
        // nudge last element: if < 1_000_000_000, increment by 1
        let mut v = vals;
        let last = v.len() - 1;
        if v[last] < 1_000_000_000 {
            v.set(last, v[last] + 1);
        }
        v
    } else {
        // fallback: identity
        vals
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

fn random_vals(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::maximum_difference(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description
    let examples: Vec<Vec<i32>> = vec![
        vec![7, 1, 5, 4],
        vec![9, 4, 3, 2],
        vec![1, 5, 2, 10],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Handcrafted edge cases
    let edges: Vec<Vec<i32>> = vec![
        vec![1, 1],                         // equal pair, result -1
        vec![2, 1],                         // decreasing, result -1
        vec![1, 2],                         // minimal positive diff
        vec![1, 1_000_000_000],             // max diff
        vec![1_000_000_000, 1],             // max to min
        vec![5, 5, 5, 5, 5],               // all same
        vec![1, 2, 3, 4, 5],               // strictly increasing
        vec![5, 4, 3, 2, 1],               // strictly decreasing
        vec![3, 1, 4, 1, 5, 9, 2, 6],      // mixed
    ];
    for e in edges {
        emit(e, &mut seen, &mut out, &mut count);
    }

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Seed arrays with various mutations
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![100, 200],
        vec![500, 300, 700],
        vec![1, 1, 1, 1],
        vec![999_999_999, 1_000_000_000],
    ];
    for s in &seed_arrays {
        for &mk in &mutation_kinds {
            let result = generate_test_case(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 5),        // tiny
            1 => rng.gen_range_usize(2, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 500),     // large
            _ => rng.gen_range_usize(501, 1000),    // max
        };
        let seed_arr = random_vals(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = generate_test_case(seed_arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
