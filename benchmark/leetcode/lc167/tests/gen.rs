use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    a_val: i32,
    b_val: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    ensures
        2 <= result.0.len() <= 30_000,
        -1_000 <= result.1 <= 1_000,
        forall|i: int|
            0 <= i < result.0.len() ==> -1_000 <= #[trigger] result.0[i] <= 1_000,
        forall |i: int, j: int|
            0 <= i < j < result.0.len() ==> result.0[i] <= result.0[j],
        exists|i: int, j: int|
            0 <= i < result.0.len() &&
            0 <= j < result.0.len() &&
            i != j &&
            result.0[i] + result.0[j] == result.1,
        forall|i1: int, j1: int, i2: int, j2: int|
            0 <= i1 < result.0.len() && 0 <= j1 < result.0.len() && i1 != j1 && 0 <= i2
                < result.0.len() && 0 <= j2 < result.0.len() && i2 != j2 && result.0[i1]
                + result.0[j1] == result.1 && result.0[i2] + result.0[j2] == result.1 ==> (i1
                == i2 && j1 == j2) || (i1 == j2 && j1 == i2),
{
    let n = if n < 2 { 2usize } else if n > 30000 { 30000usize } else { n };
    let a_val = if a_val < -1000 { -1000 } else if a_val > 498 { 498 } else { a_val };
    let low = if a_val + 3 > -1000 - a_val { a_val + 3 } else { -1000 - a_val };
    let high = if 1000 - a_val < 1000 { 1000 - a_val } else { 1000 };
    let b_val = if b_val < low { low } else if b_val > high { high } else { b_val };
    let target: i32 = a_val + b_val;

    if mutation_kind == 1u8 {
        // Mutation 1: two-element array [a_val, b_val]
        let mut nums: Vec<i32> = Vec::new();
        nums.push(a_val);
        nums.push(b_val);

        proof {
            assert(nums[0int] == a_val);
            assert(nums[1int] == b_val);
            assert(nums[0int] + nums[1int] == target);

            assert forall|i1: int, j1: int, i2: int, j2: int|
                0 <= i1 < nums.len() && 0 <= j1 < nums.len() && i1 != j1
                && 0 <= i2 < nums.len() && 0 <= j2 < nums.len() && i2 != j2
                && nums[i1] + nums[j1] == target && nums[i2] + nums[j2] == target
            implies (i1 == i2 && j1 == j2) || (i1 == j2 && j1 == i2)
            by {
                // Only indices 0 and 1 exist; only unordered pair is {0,1}
            }
        }

        let result = (nums, target);
        assert(result.0[0] + result.0[result.0.len() - 1] == result.1);
        result
    } else {
        // Mutation 0 (default): fillers = a_val + 1
        // Mutation 2: fillers = b_val - 1
        // Array: [a_val, f, f, ..., f, b_val]
        let f_val: i32 = if mutation_kind == 2u8 {
            (b_val - 1) as i32
        } else {
            (a_val + 1) as i32
        };

        proof {
            // Establish key arithmetic facts about f_val
            assert(a_val < f_val);
            assert(f_val < b_val);
            assert(-1_000 <= f_val && f_val <= 1_000);
        }

        let mut nums: Vec<i32> = Vec::new();
        nums.push(a_val);

        let mut i: usize = 1;
        while i < n - 1
            invariant
                2 <= n <= 30_000,
                1 <= i <= n - 1,
                nums.len() == i as int,
                nums[0int] == a_val,
                forall|k: int| 1 <= k < i as int ==> #[trigger] nums[k] == f_val,
                -1_000 <= a_val,
                b_val <= 1_000,
                b_val as int >= a_val as int + 3,
                a_val < f_val,
                f_val < b_val,
                -1_000 <= f_val && f_val <= 1_000,
            decreases n - 1 - i,
        {
            nums.push(f_val);
            i = i + 1;
        }

        nums.push(b_val);

        proof {
            assert(nums.len() == n as int);
            assert(nums[0int] == a_val);
            assert(nums[(n - 1) as int] == b_val);

            // All elements in bounds
            assert forall|k: int| 0 <= k < nums.len()
            implies -1_000 <= #[trigger] nums[k] <= 1_000
            by {
                if k == 0 {
                } else if k == nums.len() - 1 {
                } else {
                    assert(nums[k] == f_val);
                }
            }

            // Sortedness
            assert forall|k: int, l: int| 0 <= k < l < nums.len()
            implies nums[k] <= nums[l]
            by {
                if k == 0 {
                    if l == nums.len() - 1 {
                        assert(nums[k] == a_val && nums[l] == b_val);
                    } else {
                        assert(nums[k] == a_val && nums[l] == f_val);
                    }
                } else if l == nums.len() - 1 {
                    assert(nums[k] == f_val && nums[l] == b_val);
                } else {
                    assert(nums[k] == f_val && nums[l] == f_val);
                }
            }

            // Existence
            assert(nums[0int] + nums[(n - 1) as int] == target);

            // Uniqueness key facts
            assert(a_val as int + f_val as int != target as int);
            assert(f_val as int + b_val as int != target as int);
            assert(f_val as int + f_val as int != target as int);

            assert forall|i1: int, j1: int, i2: int, j2: int|
                0 <= i1 < nums.len() && 0 <= j1 < nums.len() && i1 != j1
                && 0 <= i2 < nums.len() && 0 <= j2 < nums.len() && i2 != j2
                && nums[i1] + nums[j1] == target && nums[i2] + nums[j2] == target
            implies (i1 == i2 && j1 == j2) || (i1 == j2 && j1 == i2)
            by {
                // Show (i1, j1) must be {0, n-1}
                if i1 == 0 {
                    if j1 != nums.len() - 1 {
                        if j1 > 0 {
                            assert(nums[j1] == f_val);
                            assert(a_val as int + f_val as int != target as int);
                        }
                    }
                } else if i1 == nums.len() - 1 {
                    if j1 != 0 {
                        if j1 != nums.len() - 1 {
                            assert(nums[j1] == f_val);
                            assert(b_val as int + f_val as int != target as int);
                        }
                    }
                } else {
                    assert(nums[i1] == f_val);
                    if j1 == 0 {
                        assert(f_val as int + a_val as int != target as int);
                    } else if j1 == nums.len() - 1 {
                        assert(f_val as int + b_val as int != target as int);
                    } else {
                        assert(nums[j1] == f_val);
                        assert(f_val as int + f_val as int != target as int);
                    }
                }
                // Show (i2, j2) must be {0, n-1}
                if i2 == 0 {
                    if j2 != nums.len() - 1 {
                        if j2 > 0 {
                            assert(nums[j2] == f_val);
                            assert(a_val as int + f_val as int != target as int);
                        }
                    }
                } else if i2 == nums.len() - 1 {
                    if j2 != 0 {
                        if j2 != nums.len() - 1 {
                            assert(nums[j2] == f_val);
                            assert(b_val as int + f_val as int != target as int);
                        }
                    }
                } else {
                    assert(nums[i2] == f_val);
                    if j2 == 0 {
                        assert(f_val as int + a_val as int != target as int);
                    } else if j2 == nums.len() - 1 {
                        assert(f_val as int + b_val as int != target as int);
                    } else {
                        assert(nums[j2] == f_val);
                        assert(f_val as int + f_val as int != target as int);
                    }
                }
            }
        }

        let result = (nums, target);
        assert(result.0[0] + result.0[result.0.len() - 1] == result.1);
        result
    }
}


pub fn example_case(which: u8) -> (result: (Vec<i32>, i32))
    ensures
        2 <= result.0.len() <= 30_000,
        -1_000 <= result.1 <= 1_000,
        forall|i: int|
            0 <= i < result.0.len() ==> -1_000 <= #[trigger] result.0[i] <= 1_000,
        forall |i: int, j: int|
            0 <= i < j < result.0.len() ==> result.0[i] <= result.0[j],
        exists|i: int, j: int|
            0 <= i < result.0.len() &&
            0 <= j < result.0.len() &&
            i != j &&
            result.0[i] + result.0[j] == result.1,
        forall|i1: int, j1: int, i2: int, j2: int|
            0 <= i1 < result.0.len() && 0 <= j1 < result.0.len() && i1 != j1 && 0 <= i2
                < result.0.len() && 0 <= j2 < result.0.len() && i2 != j2 && result.0[i1]
                + result.0[j1] == result.1 && result.0[i2] + result.0[j2] == result.1 ==> (i1
                == i2 && j1 == j2) || (i1 == j2 && j1 == i2),
{
    let mut nums: Vec<i32> = Vec::new();
    let target;
    if which == 0 {
        nums.push(2); nums.push(7); nums.push(11); nums.push(15); target = 9;
    } else if which == 1 {
        nums.push(2); nums.push(3); nums.push(4); target = 6;
    } else {
        nums.push(-1); nums.push(0); target = -1;
    }
    assert(nums[0] + nums[if which == 1 { 2int } else { 1int }] == target);
    (nums, target)
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

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(167);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($numbers:expr, $target:expr) => {
            if count < goal {
                let numbers_val: Vec<i32> = $numbers;
                let target_val: i32 = $target;
                let result = Solution::two_sum(numbers_val.clone(), target_val);
                let line = json!({
                    "input": {"numbers": numbers_val, "target": target_val},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    macro_rules! gen_emit {
        ($n:expr, $a:expr, $b:expr, $mk:expr) => {
            if count < goal {
                let (numbers, target) = generate_test_case($n as usize, $a as i32, $b as i32, $mk as u8);
                emit!(numbers, target);
            }
        };
    }

    // ---- LeetCode examples ----
    for which in 0..3 {
        let (numbers, target) = example_case(which);
        emit!(numbers, target);
    }

    // ---- Boundary value pairs, all mutations ----
    for mk in 0u8..=2 {
        gen_emit!(2, -1000, -997, mk);   // min values
        gen_emit!(2, 497, 500, mk);      // near max a_val
        gen_emit!(2, -500, 500, mk);     // symmetric around 0
        gen_emit!(2, 0, 3, mk);          // small positive
        gen_emit!(2, -3, 0, mk);         // small negative
        gen_emit!(2, -500, -497, mk);    // negative pair
    }

    // ---- Size diversity with all mutations ----
    for mk in 0u8..=2 {
        gen_emit!(3, -100, 100, mk);
        gen_emit!(5, -100, 100, mk);
        gen_emit!(10, -200, 200, mk);
        gen_emit!(50, -300, 300, mk);
        gen_emit!(100, -400, 400, mk);
        gen_emit!(500, -100, 100, mk);
        gen_emit!(1000, -200, 200, mk);
        gen_emit!(5000, -100, 100, mk);
        gen_emit!(10000, -100, 100, mk);
    }

    // ---- Target boundary values ----
    gen_emit!(2, -1000, 3, 0);       // target = -997
    gen_emit!(2, -3, 1000, 0);       // target = 997
    gen_emit!(2, -500, 500, 0);      // target = 0
    gen_emit!(5, -502, -499, 0);     // target = -1001... wait, need target in [-1000, 1000]
    gen_emit!(5, -500, 497, 0);      // target = -3
    gen_emit!(5, 497, 500, 1);       // target = 997, 2-elem mutation

    // ---- Random tiny arrays (2-5 elements) ----
    for _ in 0..6 {
        let a = rng.gen_range_i64(-400, 400) as i32;
        let b_lo = std::cmp::max(a as i64 + 3, -1000 - a as i64);
        let b_hi = std::cmp::min(1000i64, 1000 - a as i64);
        if b_lo > b_hi { continue; }
        let b = rng.gen_range_i64(b_lo, b_hi) as i32;
        let n = rng.gen_range_usize(2, 5);
        for mk in 0u8..=2 {
            gen_emit!(n, a, b, mk);
        }
    }

    // ---- Random small arrays (6-20 elements) ----
    for _ in 0..5 {
        let a = rng.gen_range_i64(-400, 400) as i32;
        let b_lo = std::cmp::max(a as i64 + 3, -1000 - a as i64);
        let b_hi = std::cmp::min(1000i64, 1000 - a as i64);
        if b_lo > b_hi { continue; }
        let b = rng.gen_range_i64(b_lo, b_hi) as i32;
        let n = rng.gen_range_usize(6, 20);
        let mk = rng.gen_range_i64(0, 2) as u8;
        gen_emit!(n, a, b, mk);
    }

    // ---- Random medium arrays (21-200 elements) ----
    for _ in 0..5 {
        let a = rng.gen_range_i64(-400, 400) as i32;
        let b_lo = std::cmp::max(a as i64 + 3, -1000 - a as i64);
        let b_hi = std::cmp::min(1000i64, 1000 - a as i64);
        if b_lo > b_hi { continue; }
        let b = rng.gen_range_i64(b_lo, b_hi) as i32;
        let n = rng.gen_range_usize(21, 200);
        let mk = rng.gen_range_i64(0, 2) as u8;
        gen_emit!(n, a, b, mk);
    }

    // ---- Random large arrays (201-5000 elements) ----
    for _ in 0..4 {
        let a = rng.gen_range_i64(-400, 400) as i32;
        let b_lo = std::cmp::max(a as i64 + 3, -1000 - a as i64);
        let b_hi = std::cmp::min(1000i64, 1000 - a as i64);
        if b_lo > b_hi { continue; }
        let b = rng.gen_range_i64(b_lo, b_hi) as i32;
        let n = rng.gen_range_usize(201, 5000);
        let mk = rng.gen_range_i64(0, 2) as u8;
        gen_emit!(n, a, b, mk);
    }

    // ---- Maximum size (10000 elements) ----
    for mk in 0u8..=2 {
        gen_emit!(10000, -200, 200, mk);
        gen_emit!(10000, -500, 500, mk);
    }

    // ---- Fill remaining with random sizes and values ----
    while count < goal {
        let n = match rng.gen_range_i64(0, 4) {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(6, 50),
            2 => rng.gen_range_usize(51, 500),
            3 => rng.gen_range_usize(501, 2000),
            _ => rng.gen_range_usize(2001, 10000),
        };
        let a = rng.gen_range_i64(-498, 498) as i32;
        let b_lo = std::cmp::max(a as i64 + 3, -1000 - a as i64);
        let b_hi = std::cmp::min(1000i64, 1000 - a as i64);
        if b_lo > b_hi { continue; }
        let b = rng.gen_range_i64(b_lo, b_hi) as i32;
        let mk = rng.gen_range_i64(0, 2) as u8;
        gen_emit!(n, a, b, mk);
    }
}
