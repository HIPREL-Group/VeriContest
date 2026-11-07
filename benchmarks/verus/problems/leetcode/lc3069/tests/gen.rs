use vstd::prelude::*;

verus! {

pub fn generate_test_case(len: usize, start: i32, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        3 <= len <= 50,
        1 <= start,
        start as int + len as int - 1 <= 100,
    ensures
        3 <= result.len() <= 50,
        forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
        forall |i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    // Build consecutive array [start, start+1, ..., start+len-1]
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < len
        invariant
            k <= len,
            nums.len() == k as int,
            3 <= len <= 50,
            1 <= start,
            start as int + len as int - 1 <= 100,
            forall |i: int| 0 <= i < k as int ==> nums[i] == (start + i as i32),
        decreases len - k,
    {
        assert(start as int + k as int <= 100);
        assert(k < len);
        nums.push((start + k as i32));
        k += 1;
    }

    proof {
        assert forall |i: int| 0 <= i < nums@.len() implies 1 <= #[trigger] nums[i] <= 100 by {
            assert(nums[i] == start + i as i32);
            assert(start as int + i >= 1);
            assert(start as int + i <= start as int + len as int - 1);
        };
        assert forall |i: int, j: int| 0 <= i < j < nums@.len() implies nums[i] != nums[j] by {
            assert(nums[i] == start + i as i32);
            assert(nums[j] == start + j as i32);
        };
    }

    if mutation_kind == 1 {
        // Swap elements at indices 0 and 1
        let v0 = nums[0];
        let v1 = nums[1];

        assert(v0 == start);
        assert(v1 == start + 1i32);

        let ghost pre = nums@;

        nums.set(0, v1);

        assert(nums[0] == v1);
        assert forall |j: int| 1 <= j < nums@.len() implies nums[j] == pre[j] by {};

        nums.set(1, v0);

        assert(nums[0] == v1);
        assert(nums[1] == v0);

        proof {
            assert forall |i: int| 0 <= i < nums@.len() implies 1 <= #[trigger] nums[i] <= 100 by {
                if i == 0 {
                    assert(nums[i] == v1);
                    assert(v1 == start + 1i32);
                } else if i == 1 {
                    assert(nums[i] == v0);
                    assert(v0 == start);
                } else {
                    assert(nums[i] == pre[i]);
                    assert(pre[i] == start + i as i32);
                }
            };
            assert forall |i: int, j: int| 0 <= i < j < nums@.len() implies nums[i] != nums[j] by {
                if i == 0 && j == 1 {
                    assert(nums[0] == start + 1i32);
                    assert(nums[1] == start);
                } else if i == 0 {
                    assert(nums[0] == start + 1i32);
                    assert(nums[j] == pre[j]);
                    assert(pre[j] == start + j as i32);
                    assert(j >= 2);
                } else if i == 1 {
                    assert(nums[1] == start);
                    assert(nums[j] == pre[j]);
                    assert(pre[j] == start + j as i32);
                    assert(j >= 2);
                } else {
                    assert(nums[i] == pre[i]);
                    assert(pre[i] == start + i as i32);
                    assert(nums[j] == pre[j]);
                    assert(pre[j] == start + j as i32);
                }
            };
        }
        nums
    } else if mutation_kind == 2 {
        // Swap elements at indices 0 and len-1
        let last_idx = len - 1;
        let v0 = nums[0];
        let vl = nums[last_idx];

        assert(v0 == start);
        assert(vl == start + last_idx as i32);
        assert(last_idx >= 2);

        let ghost pre = nums@;

        nums.set(0, vl);

        assert(nums[0] == vl);
        assert forall |j: int| 1 <= j < nums@.len() implies nums[j] == pre[j] by {};

        nums.set(last_idx, v0);

        assert(nums[last_idx as int] == v0);
        assert(nums[0] == vl);

        proof {
            assert forall |k: int| 1 <= k < last_idx as int implies nums[k] == pre[k] by {};

            assert forall |i: int| 0 <= i < nums@.len() implies 1 <= #[trigger] nums[i] <= 100 by {
                if i == 0 {
                    assert(nums[i] == vl);
                    assert(vl == start + last_idx as i32);
                } else if i == last_idx as int {
                    assert(nums[i] == v0);
                    assert(v0 == start);
                } else {
                    assert(nums[i] == pre[i]);
                    assert(pre[i] == start + i as i32);
                }
            };
            assert forall |i: int, j: int| 0 <= i < j < nums@.len() implies nums[i] != nums[j] by {
                if i == 0 && j == last_idx as int {
                    assert(nums[0] == start + last_idx as i32);
                    assert(nums[last_idx as int] == start);
                    assert(last_idx >= 2);
                } else if i == 0 {
                    assert(nums[0] == start + last_idx as i32);
                    assert(nums[j] == pre[j]);
                    assert(pre[j] == start + j as i32);
                    assert(j != last_idx as int);
                } else if j == last_idx as int {
                    assert(nums[i] == pre[i]);
                    assert(pre[i] == start + i as i32);
                    assert(nums[last_idx as int] == start);
                    assert(i >= 1);
                } else {
                    assert(nums[i] == pre[i]);
                    assert(pre[i] == start + i as i32);
                    assert(nums[j] == pre[j]);
                    assert(pre[j] == start + j as i32);
                }
            };
        }
        nums
    } else {
        // identity
        nums
    }
}

} // verus!

fn gen(len: usize, start: i32, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(len, start, mutation_kind)
}

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

    let mut emit = |nums: Vec<i32>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let output = Solution::result_array(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description
    emit(vec![2, 1, 3], &mut out, &mut total);
    emit(vec![5, 4, 3, 8], &mut out, &mut total);

    let mutation_kinds: Vec<u8> = vec![0, 1, 2];

    // Structured: size classes x start positions x mutations
    let sizes: Vec<usize> = vec![3, 4, 5, 7, 10, 15, 20, 30, 40, 50];

    for &sz in &sizes {
        let max_start = (101 - sz) as i32;
        for &mk in &mutation_kinds {
            emit(gen(sz, 1, mk), &mut out, &mut total);
            emit(gen(sz, max_start, mk), &mut out, &mut total);
            let mid = std::cmp::max(max_start / 2, 1);
            emit(gen(sz, mid, mk), &mut out, &mut total);
        }
    }

    // Random construction parameters with size-class diversity
    while total < count {
        let sz = match total % 5 {
            0 => rng.gen_range_usize(3, 5),
            1 => rng.gen_range_usize(3, 10),
            2 => rng.gen_range_usize(11, 25),
            3 => rng.gen_range_usize(26, 40),
            _ => rng.gen_range_usize(41, 50),
        };
        let max_start = (101 - sz) as i64;
        let start = rng.gen_range_i64(1, max_start) as i32;
        let mk = rng.gen_range_usize(0, 2) as u8;
        emit(gen(sz, start, mk), &mut out, &mut total);
    }
}
