use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: u32, base: u32, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= n <= 100,
        1 <= base,
        base as int + n as int - 1 <= 100,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let mut nums: Vec<i32> = Vec::new();
    let mut k: u32 = 0;
    while k < n
        invariant
            0 <= k <= n,
            nums.len() == k as int,
            1 <= n <= 100,
            1 <= base,
            base as int + n as int - 1 <= 100,
            forall|i: int| 0 <= i < k as int ==> nums[i] == (base as int + i),
            forall|i: int| 0 <= i < k as int ==> 1 <= #[trigger] nums[i] <= 100,
            forall|i: int, j: int| 0 <= i < j < k as int ==> nums[i] != nums[j],
        decreases n - k,
    {
        let val = (base + k) as i32;
        proof {
            assert forall|i: int| 0 <= i < k as int implies nums[i] != val by {
                assert(nums[i] == (base as int + i));
                assert(val == (base as int + k as int));
            };
        }
        nums.push(val);
        k += 1;
    }

    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 && nums.len() > 1 {
        // shrink: pop last element
        nums.pop();
        nums
    } else if mutation_kind == 2 && base + n <= 100 && n < 100 {
        // grow: push base + n
        let new_val = (base + n) as i32;
        proof {
            assert forall|i: int| 0 <= i < nums.len() as int implies #[trigger] nums[i] != new_val by {
                assert(nums[i] == (base as int + i));
                assert(new_val == (base as int + n as int));
            };
        }
        nums.push(new_val);
        nums
    } else if mutation_kind == 3 && nums.len() >= 2 {
        // swap first and last
        let last = nums.len() - 1;
        let v0 = nums[0];
        let vlast = nums[last];
        nums.set(0, vlast);
        nums.set(last, v0);
        proof {
            assert forall|i: int, j: int| 0 <= i < j < nums.len() as int implies nums[i] != nums[j] by {
                if i == 0 && j == last as int {
                    assert(nums[0] == vlast);
                    assert(nums[last as int] == v0);
                    assert(vlast == (base as int + last as int));
                    assert(v0 == base as int);
                } else if i == 0 {
                    assert(nums[0] == vlast);
                    assert(vlast == (base as int + last as int));
                    assert(nums[j] == (base as int + j));
                    assert(j != last as int);
                } else if j == last as int {
                    assert(nums[last as int] == v0);
                    assert(v0 == base as int);
                    assert(nums[i] == (base as int + i));
                    assert(i != 0int);
                } else {
                    assert(nums[i] == (base as int + i));
                    assert(nums[j] == (base as int + j));
                }
            };
        }
        nums
    } else if mutation_kind == 4 && base > 1 {
        // replace first element with base - 1
        let new_val = (base - 1) as i32;
        nums.set(0, new_val);
        proof {
            assert forall|i: int, j: int| 0 <= i < j < nums.len() as int implies nums[i] != nums[j] by {
                if i == 0 {
                    assert(nums[0] == new_val);
                    assert(new_val == (base as int - 1));
                    assert(nums[j] == (base as int + j));
                    assert(j >= 1);
                } else {
                    assert(nums[i] == (base as int + i));
                    assert(nums[j] == (base as int + j));
                }
            };
        }
        nums
    } else if mutation_kind == 5 && base + n <= 100 {
        // replace last element with base + n
        let last = nums.len() - 1;
        let new_val = (base + n) as i32;
        nums.set(last, new_val);
        proof {
            assert forall|i: int, j: int| 0 <= i < j < nums.len() as int implies nums[i] != nums[j] by {
                if j == last as int {
                    assert(nums[last as int] == new_val);
                    assert(new_val == (base as int + n as int));
                    assert(nums[i] == (base as int + i));
                    assert(i < last as int);
                } else {
                    assert(nums[i] == (base as int + i));
                    assert(nums[j] == (base as int + j));
                }
            };
        }
        nums
    } else {
        // fallback: identity
        nums
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn gen(n: u32, base: u32, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(n, base, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2733);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::find_non_min_or_max(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![3, 2, 1, 4],
        vec![1, 2],
        vec![2, 1, 3],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Seed arrays: various (n, base) combos with all mutation kinds
    let configs: Vec<(u32, u32)> = vec![
        (1, 1), (1, 100), (2, 1), (2, 99), (3, 1), (3, 50),
        (5, 1), (10, 1), (10, 91), (50, 1), (50, 51), (100, 1),
        (20, 40), (3, 98),
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    for &(n, base) in &configs {
        for &mk in &mutation_kinds {
            let valid = match mk {
                0 => true,
                1 => n > 1,
                2 => (base as u64 + n as u64) <= 100 && n < 100,
                3 => n >= 2,
                4 => base > 1,
                5 => (base as u64 + n as u64) <= 100,
                _ => false,
            };
            if valid {
                let nums = gen(n, base, mk);
                emit(nums, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random test cases to fill remaining slots
    let mut _attempts_0 = 0usize;
    while count < target {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 3) as u32,
            1 => rng.gen_range_usize(1, 10) as u32,
            2 => rng.gen_range_usize(10, 50) as u32,
            3 => rng.gen_range_usize(50, 100) as u32,
            _ => 100u32,
        };
        let max_base = (101 - n) as usize;
        let base = rng.gen_range_usize(1, max_base) as u32;
        let mk = rng.gen_range_usize(0, 5) as u8;
        let nums = gen(n, base, mk);
        emit(nums, &mut seen, &mut out, &mut count);
    }
}
