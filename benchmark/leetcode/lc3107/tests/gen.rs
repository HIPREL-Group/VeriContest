use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: Vec<i32>, k: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= vals.len() <= 200000,
        1 <= k <= 1000000000,
        forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1000000000,
    ensures
        1 <= result.0.len() <= 200000,
        1 <= result.1 <= 1000000000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000000000,
{
    if mutation_kind == 0 {
        // identity
        (vals, k)
    } else if mutation_kind == 1 {
        // set first element to k
        let mut d = vals;
        d.set(0, k);
        (d, k)
    } else if mutation_kind == 2 {
        // set all elements to k (median equals k, cost 0)
        let mut d = vals;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == vals.len(),
                1 <= d.len() <= 200000,
                1 <= k <= 1000000000,
                forall|j: int| 0 <= j < d.len() ==> 1 <= #[trigger] d[j] <= 1000000000,
            decreases d.len() - i,
        {
            d.set(i, k);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 3 {
        // set middle element to k (force median toward k)
        let mid = vals.len() / 2;
        let mut d = vals;
        d.set(mid, k);
        (d, k)
    } else if mutation_kind == 4 {
        // k = 1 (minimum boundary)
        (vals, 1i32)
    } else if mutation_kind == 5 {
        // k = 1_000_000_000 (maximum boundary)
        (vals, 1000000000i32)
    } else if mutation_kind == 6 && k < 1000000000 {
        // nudge k up
        (vals, (k + 1) as i32)
    } else if mutation_kind == 7 && k > 1 {
        // nudge k down
        (vals, (k - 1) as i32)
    } else if mutation_kind == 8 {
        // set first element to 1 (min element boundary)
        let mut d = vals;
        d.set(0, 1i32);
        (d, k)
    } else if mutation_kind == 9 {
        // set first element to 1_000_000_000 (max element boundary)
        let mut d = vals;
        d.set(0, 1000000000i32);
        (d, k)
    } else {
        // fallback: identity
        (vals, k)
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

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    arr
}

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut total = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let output = Solution::min_operations_to_make_median_k(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    emit(vec![2, 5, 6, 8, 5], 4, &mut out, &mut total);
    emit(vec![2, 5, 6, 8, 5], 7, &mut out, &mut total);
    emit(vec![1, 2, 3, 4, 5, 6], 4, &mut out, &mut total);

    // Seed arrays with interesting structure
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1_000_000_000],
        vec![1, 1_000_000_000],
        vec![500_000_000],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![1, 1, 1, 1, 1],
        vec![1_000_000_000, 1_000_000_000, 1_000_000_000],
        vec![1, 1, 1],
        vec![100, 200, 300, 400, 500, 600, 700],
    ];
    let k_values: Vec<i32> = vec![1, 2, 500_000_000, 999_999_999, 1_000_000_000];
    let mutation_kinds: Vec<u8> = (0..=9).collect();

    for arr in &seed_arrays {
        for &k in &k_values {
            for &mk in &mutation_kinds {
                if total >= count { break; }
                let (nums, k_out) = generate_test_case(arr.clone(), k, mk);
                emit(nums, k_out, &mut out, &mut total);
            }
        }
    }

    // Random test cases with diverse size classes
    while total < count {
        // Size classes: tiny, small, medium, large, big
        let n = match total % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 2000),
        };

        // Mix in boundary k values ~30% of the time
        let k = match rng.next_u64() % 10 {
            0 => 1i32,
            1 => 1_000_000_000i32,
            2 => 500_000_000i32,
            _ => rng.gen_range_i64(1, 1_000_000_000) as i32,
        };

        let vals = random_array(&mut rng, n);
        let mk = (rng.next_u64() % 10) as u8;
        let (nums, k_out) = generate_test_case(vals, k, mk);
        emit(nums, k_out, &mut out, &mut total);
    }
}
