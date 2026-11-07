use vstd::prelude::*;

verus! {

pub open spec fn contains(nums: Seq<i32>, value: i32) -> bool {
    exists |j: int| 0 <= j < nums.len() && #[trigger] nums[j] == value
}

pub fn generate_test_case(n: usize, missing: usize, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= n <= 10_000,
        0 <= missing <= n,
    ensures
        1 <= result.len() <= 10_000,
        forall |i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= result.len(),
        forall |i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
        exists |k: int| 0 <= k <= result.len() && !(#[trigger] contains(result@, k as i32)),
{
    // Select which value to omit based on mutation_kind
    let m: usize = if mutation_kind == 1 {
        0usize
    } else if mutation_kind == 2 {
        n
    } else if mutation_kind == 3 && n >= 2 {
        n / 2
    } else if mutation_kind == 4 && n >= 2 {
        1usize
    } else if mutation_kind == 5 && n >= 2 {
        n - 1
    } else {
        missing
    };

    // Build array: values 0..=n, skipping m
    // Result has n elements: indices 0..m map to values 0..m,
    //                        indices m..n-1 map to values m+1..n
    let mut nums: Vec<i32> = Vec::new();
    let mut val: usize = 0;
    while val <= n
        invariant
            0 <= val <= n + 1,
            1 <= n <= 10_000,
            0 <= m <= n,
            val <= m ==> nums.len() == val,
            val > m ==> nums.len() == val - 1,
            forall |j: int| 0 <= j < nums.len() ==> (
                #[trigger] nums[j] == (if j < m as int { j } else { j + 1 }) as i32
            ),
            forall |j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= n as int,
        decreases n + 1 - val,
    {
        if val != m {
            nums.push(val as i32);
        }
        val = val + 1;
    }

    proof {
        assert(nums.len() == n as int);

        // Prove distinctness: values are strictly increasing
        assert forall |i: int, j: int| 0 <= i < j < nums.len()
            implies nums[i] != nums[j]
        by {
            let vi = if i < m as int { i } else { i + 1 };
            let vj = if j < m as int { j } else { j + 1 };
            assert(nums[i] == vi as i32);
            assert(nums[j] == vj as i32);
            // i < j implies vi < vj in all cases
            if i < m as int && j < m as int {
                assert(vi < vj);
            } else if i < m as int && j >= m as int {
                assert(vi == i);
                assert(vj == j + 1);
                assert(i < j);
                assert(vi < vj);
            } else {
                assert(vi == i + 1);
                assert(vj == j + 1);
                assert(vi < vj);
            }
        };

        // Prove m is not contained in nums
        assert forall |j: int| 0 <= j < nums.len()
            implies nums[j] != m as i32
        by {
            if j < m as int {
                assert(nums[j] == j as i32);
            } else {
                assert(nums[j] == (j + 1) as i32);
            }
        };

        assert(!contains(nums@, m as i32));
        assert(0 <= m as int <= nums.len());
    }

    nums
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut generated = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, generated: &mut usize| {
        if *generated >= count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::missing_number(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *generated += 1;
    };

    // Example test cases from description.md
    emit(vec![3, 0, 1], &mut seen, &mut out, &mut generated);
    emit(vec![0, 1], &mut seen, &mut out, &mut generated);
    emit(vec![9, 6, 4, 2, 3, 5, 7, 0, 1], &mut seen, &mut out, &mut generated);

    // Boundary: n=1
    for mk in 0u8..=5 {
        let nums = generate_test_case(1, 0, mk);
        emit(nums, &mut seen, &mut out, &mut generated);
        let nums = generate_test_case(1, 1, mk);
        emit(nums, &mut seen, &mut out, &mut generated);
    }

    // Small arrays with all mutation kinds
    for n in [2usize, 3, 5, 10] {
        for missing in [0, n / 2, n] {
            for mk in 0u8..=5 {
                let mut nums = generate_test_case(n, missing, mk);
                // Shuffle for structural diversity
                for i in (1..nums.len()).rev() {
                    let j = rng.gen_range_usize(0, i);
                    let a = nums[i];
                    let b = nums[j];
                    nums[i] = b;
                    nums[j] = a;
                }
                emit(nums, &mut seen, &mut out, &mut generated);
            }
        }
    }

    // Random test cases across size classes
    while generated < count {
        let n = match generated % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let missing = rng.gen_range_usize(0, n);
        let mk = (rng.next_u64() % 6) as u8;

        let mut nums = generate_test_case(n, missing, mk);

        // Shuffle for diversity
        for i in (1..nums.len()).rev() {
            let j = rng.gen_range_usize(0, i);
            let a = nums[i];
            let b = nums[j];
            nums[i] = b;
            nums[j] = a;
        }

        emit(nums, &mut seen, &mut out, &mut generated);
    }
}
