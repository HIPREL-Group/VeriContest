use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    base_nums: Vec<i32>,
    pivot: i32,
    pivot_idx: usize,
    mutation_kind: u8,
) -> (nums: Vec<i32>)
    requires
        1 <= base_nums.len() <= 100_000,
        forall|i: int| 0 <= i < base_nums.len() ==> -1_000_000 <= #[trigger] base_nums[i] <= 1_000_000,
        -1_000_000 <= pivot <= 1_000_000,
        pivot_idx < base_nums.len(),
        base_nums[pivot_idx as int] == pivot,
    ensures
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> -1_000_000 <= #[trigger] nums[i] <= 1_000_000,
        exists|i: int| 0 <= i < nums.len() && nums[i] == pivot,
{
    if mutation_kind == 0 {
        // identity
        assert(base_nums[pivot_idx as int] == pivot);
        base_nums
    } else if mutation_kind == 1 {
        // set all elements to pivot
        let n = base_nums.len();
        let mut d: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                d.len() == i,
                1 <= n <= 100_000,
                -1_000_000 <= pivot <= 1_000_000,
                forall|j: int| 0 <= j < i ==> #[trigger] d[j] == pivot,
            decreases n - i,
        {
            d.push(pivot);
            i += 1;
        }
        assert(d[0int] == pivot);
        d
    } else if mutation_kind == 2 && base_nums.len() < 100_000 {
        // grow: push pivot value at end
        let mut d = base_nums;
        d.push(pivot);
        let last = d.len() - 1;
        assert(d[last as int] == pivot);
        d
    } else if mutation_kind == 3 && base_nums.len() > 1 && pivot_idx < base_nums.len() - 1 {
        // shrink: pop last element (pivot_idx is not last, so pivot remains)
        let mut d = base_nums;
        d.pop();
        assert(d[pivot_idx as int] == pivot);
        d
    } else if mutation_kind == 4 {
        // set first element to pivot value
        let mut d = base_nums;
        d.set(0, pivot);
        assert(d[0int] == pivot);
        d
    } else if mutation_kind == 5 {
        // set last element to pivot value
        let mut d = base_nums;
        let last = d.len() - 1;
        d.set(last, pivot);
        assert(d[last as int] == pivot);
        d
    } else if mutation_kind == 6 && base_nums.len() >= 2 && pivot_idx > 0 && base_nums[0] < 1_000_000 {
        // nudge first element up (pivot_idx > 0, so pivot untouched)
        let v = base_nums[0] + 1;
        let mut d = base_nums;
        d.set(0, v);
        assert(d[pivot_idx as int] == pivot);
        d
    } else if mutation_kind == 7 && base_nums.len() >= 2 && pivot_idx > 0 && base_nums[0] > -1_000_000 {
        // nudge first element down (pivot_idx > 0, so pivot untouched)
        let v = base_nums[0] - 1;
        let mut d = base_nums;
        d.set(0, v);
        assert(d[pivot_idx as int] == pivot);
        d
    } else {
        // fallback: identity
        assert(base_nums[pivot_idx as int] == pivot);
        base_nums
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

extern crate serde_json;
use serde_json::json;

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(-1_000_000, 1_000_000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2161);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, pivot: i32, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let output = Solution::pivot_array(nums.clone(), pivot);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "pivot": pivot},
            "output": output
        })).unwrap();
        *emitted += 1;
    };

    // Example test cases from description.md
    emit(vec![9, 12, 5, 10, 14, 3, 10], 10, &mut out, &mut emitted);
    emit(vec![-3, 4, 3, 2], 2, &mut out, &mut emitted);

    // Structured seeds with all mutations
    let seed_arrays: Vec<(Vec<i32>, usize)> = vec![
        (vec![1], 0),
        (vec![0, 0, 0], 1),
        (vec![-1_000_000, 0, 1_000_000], 0),
        (vec![-1_000_000, 0, 1_000_000], 2),
        (vec![5, 5, 5, 5, 5], 2),
        (vec![1, 2, 3, 4, 5], 0),
        (vec![1, 2, 3, 4, 5], 4),
        (vec![1, 2, 3, 4, 5], 2),
        (vec![10, -10, 10, -10], 0),
        (vec![10, -10, 10, -10], 1),
        (vec![999_999, 1_000_000, -999_999], 1),
        (vec![-1, -1, -1, 0, 1, 1, 1], 3),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    for (seed_nums, seed_pidx) in &seed_arrays {
        let piv = seed_nums[*seed_pidx];
        for &mk in &mutation_kinds {
            if emitted >= count {
                break;
            }
            let result_nums = generate_test_case(seed_nums.clone(), piv, *seed_pidx, mk);
            emit(result_nums, piv, &mut out, &mut emitted);
        }
    }

    // Random test cases across size classes
    while emitted < count {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // big
        };
        let base = random_array(&mut rng, n);
        let pidx = rng.gen_range_usize(0, n - 1);
        let piv = base[pidx];
        let mk = rng.gen_range_usize(0, 7) as u8;
        let result_nums = generate_test_case(base, piv, pidx, mk);
        emit(result_nums, piv, &mut out, &mut emitted);
    }
}
