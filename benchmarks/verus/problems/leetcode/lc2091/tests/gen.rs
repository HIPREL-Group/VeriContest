use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: u32,
    base: i32,
    mutation_kind: u8,
) -> (nums: Vec<i32>)
    requires
        1 <= n <= 100_000,
        -100_000 <= base,
        base as int + n as int - 1 <= 100_000,
    ensures
        1 <= nums.len() <= 100_000,
        forall |i: int, j: int| 0 <= i < j < nums.len() ==> #[trigger] nums[i] != #[trigger] nums[j],
        forall |i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
{
    let mut nums: Vec<i32> = Vec::new();

    if mutation_kind == 1 {
        // Descending: nums[k] = base + (n - 1 - k)
        let mut i: u32 = 0;
        while i < n
            invariant
                0 <= i <= n,
                nums.len() == i as int,
                1 <= n <= 100_000,
                -100_000 <= base,
                base as int + n as int - 1 <= 100_000,
                forall |k: int| 0 <= k < i as int ==>
                    (#[trigger] nums[k]) as int == base as int + (n as int - 1 - k),
                forall |k: int| 0 <= k < nums.len() ==>
                    -100_000 <= #[trigger] nums[k] <= 100_000,
            decreases n - i,
        {
            let offset = (n - 1 - i) as i32;
            let val = base + offset;
            nums.push(val);
            i += 1;
        }

        proof {
            assert forall |k: int, l: int| 0 <= k < l < nums.len()
                implies #[trigger] nums[k] != #[trigger] nums[l] by {
                assert(nums[k] as int == base as int + (n as int - 1 - k));
                assert(nums[l] as int == base as int + (n as int - 1 - l));
            };
        }
    } else {
        // Ascending: nums[k] = base + k
        let mut i: u32 = 0;
        while i < n
            invariant
                0 <= i <= n,
                nums.len() == i as int,
                1 <= n <= 100_000,
                -100_000 <= base,
                base as int + n as int - 1 <= 100_000,
                forall |k: int| 0 <= k < i as int ==>
                    (#[trigger] nums[k]) as int == base as int + k,
                forall |k: int| 0 <= k < nums.len() ==>
                    -100_000 <= #[trigger] nums[k] <= 100_000,
            decreases n - i,
        {
            let val = base + i as i32;
            nums.push(val);
            i += 1;
        }

        proof {
            assert forall |k: int, l: int| 0 <= k < l < nums.len()
                implies #[trigger] nums[k] != #[trigger] nums[l] by {
                assert(nums[k] as int == base as int + k);
                assert(nums[l] as int == base as int + l);
            };
        }
    }

    nums
}

} // verus!

extern crate serde_json;
use serde_json::json;
use std::io::Write;
use std::collections::HashSet;

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

fn shuffle(rng: &mut Rng, nums: &mut Vec<i32>) {
    let n = nums.len();
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        nums.swap(i, j);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    macro_rules! emit {
        ($nums:expr) => {
            if emitted < count {
                let nums: Vec<i32> = $nums;
                let result = Solution::minimum_deletions(nums.clone());
                let line = json!({
                    "input": {"nums": nums},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    emitted += 1;
                }
            }
        };
    }

    // ---- Example inputs from description.md ----
    emit!(vec![2, 10, 7, 5, 4, 1, 8, 6]);
    emit!(vec![0, -4, 19, 1, 8, -2, -3, 5]);
    emit!(vec![101]);

    // ---- Single-element arrays with boundary values ----
    for &v in &[0i32, 1, -1, 100_000, -100_000, 42, -42, 99_999, -99_999] {
        emit!(vec![v]);
    }

    // ---- Two-element arrays ----
    for &(a, b) in &[
        (1i32, 2), (-1, 1), (0, 100_000), (-100_000, 0),
        (99_999, 100_000), (-100_000, 100_000),
    ] {
        emit!(vec![a, b]);
        emit!(vec![b, a]);
    }

    // ---- Small arrays (3-10), ascending and descending, shuffled ----
    for _ in 0..10 {
        let n = rng.gen_range_usize(3, 10) as u32;
        let max_base = 100_000i64 - n as i64 + 1;
        let base = rng.gen_range_i64(-100_000, max_base) as i32;
        for mk in 0u8..=1 {
            let mut nums = generate_test_case(n, base, mk);
            shuffle(&mut rng, &mut nums);
            emit!(nums);
        }
    }

    // ---- Small sorted arrays (ascending/descending without shuffle) ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(3, 20) as u32;
        let max_base = 100_000i64 - n as i64 + 1;
        let base = rng.gen_range_i64(-100_000, max_base) as i32;
        emit!(generate_test_case(n, base, 0));
        emit!(generate_test_case(n, base, 1));
    }

    // ---- Medium arrays (11-500), shuffled ----
    for _ in 0..10 {
        let n = rng.gen_range_usize(11, 500) as u32;
        let max_base = 100_000i64 - n as i64 + 1;
        let base = rng.gen_range_i64(-100_000, max_base) as i32;
        let mk = rng.gen_range_usize(0, 1) as u8;
        let mut nums = generate_test_case(n, base, mk);
        shuffle(&mut rng, &mut nums);
        emit!(nums);
    }

    // ---- Large arrays (501-10000), shuffled ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(501, 10_000) as u32;
        let max_base = 100_000i64 - n as i64 + 1;
        let base = rng.gen_range_i64(-100_000, max_base) as i32;
        let mk = rng.gen_range_usize(0, 1) as u8;
        let mut nums = generate_test_case(n, base, mk);
        shuffle(&mut rng, &mut nums);
        emit!(nums);
    }

    // ---- Very large arrays (10001-100000), shuffled ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(10_001, 100_000) as u32;
        let max_base = 100_000i64 - n as i64 + 1;
        let base = rng.gen_range_i64(-100_000, max_base) as i32;
        let mut nums = generate_test_case(n, base, 0);
        shuffle(&mut rng, &mut nums);
        emit!(nums);
    }

    // ---- Maximum size array ----
    {
        let mut nums = generate_test_case(100_000, -50_000, 0);
        shuffle(&mut rng, &mut nums);
        emit!(nums);
    }

    // ---- Boundary-spanning arrays ----
    {
        let mut nums = generate_test_case(100_000, -100_000, 0);
        shuffle(&mut rng, &mut nums);
        emit!(nums);
    }
    {
        let mut nums = generate_test_case(100_000, 1, 0);
        shuffle(&mut rng, &mut nums);
        emit!(nums);
    }

    // ---- Fill remaining with random sizes, shuffled ----
    while emitted < count {
        let size_class = rng.gen_range_usize(0, 4);
        let n = match size_class {
            0 => rng.gen_range_usize(1, 5) as u32,
            1 => rng.gen_range_usize(6, 50) as u32,
            2 => rng.gen_range_usize(51, 500) as u32,
            3 => rng.gen_range_usize(501, 5000) as u32,
            _ => rng.gen_range_usize(5001, 50_000) as u32,
        };
        let max_base = 100_000i64 - n as i64 + 1;
        let base = rng.gen_range_i64(-100_000, max_base) as i32;
        let mk = rng.gen_range_usize(0, 1) as u8;
        let mut nums = generate_test_case(n, base, mk);
        shuffle(&mut rng, &mut nums);
        emit!(nums);
    }
}
