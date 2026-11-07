use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    base: i32,
    len: u32,
    k_val: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= len <= 500,
        1 <= base <= 100_000i32,
        base as int + len as int - 1 <= 100_000,
        1 <= k_val <= len as i32,
    ensures
        1 <= result.0.len() <= 500,
        1 <= result.1 <= result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
{
    if mutation_kind == 0 {
        // Build a fully consecutive array: base, base+1, ..., base+len-1
        let mut nums: Vec<i32> = Vec::new();
        let mut i: u32 = 0;
        while i < len
            invariant
                0 <= i <= len,
                nums.len() == i as int,
                1 <= len <= 500,
                1 <= base <= 100_000i32,
                base as int + len as int - 1 <= 100_000,
                forall|j: int| 0 <= j < i as int ==>
                    #[trigger] nums[j] == (base + j as i32),
                forall|j: int| 0 <= j < nums.len() ==>
                    1 <= #[trigger] nums[j] <= 100_000,
            decreases len - i,
        {
            let val = base + (i as i32);
            assert(1 <= val <= 100_000) by {
                assert(val as int == base as int + i as int);
                assert(base as int + i as int <= base as int + len as int - 1);
            };
            nums.push(val);
            i = i + 1;
        }
        (nums, k_val)
    } else if mutation_kind == 1 {
        // Build an array where all elements are the same value (base)
        let mut nums: Vec<i32> = Vec::new();
        let mut i: u32 = 0;
        while i < len
            invariant
                0 <= i <= len,
                nums.len() == i as int,
                1 <= len <= 500,
                1 <= base <= 100_000i32,
                forall|j: int| 0 <= j < nums.len() ==>
                    #[trigger] nums[j] == base,
                forall|j: int| 0 <= j < nums.len() ==>
                    1 <= #[trigger] nums[j] <= 100_000,
            decreases len - i,
        {
            nums.push(base);
            i = i + 1;
        }
        (nums, k_val)
    } else if mutation_kind == 2 && (base as i64) + 2 * (len as i64) - 2 <= 100_000 {
        // Build array with step 2: base, base+2, base+4, ...
        let mut nums: Vec<i32> = Vec::new();
        let mut i: u32 = 0;
        while i < len
            invariant
                0 <= i <= len,
                nums.len() == i as int,
                1 <= len <= 500,
                1 <= base <= 100_000i32,
                base as int + 2 * (len as int) - 2 <= 100_000,
                forall|j: int| 0 <= j < i as int ==>
                    #[trigger] nums[j] == (base + 2 * j as i32),
                forall|j: int| 0 <= j < nums.len() ==>
                    1 <= #[trigger] nums[j] <= 100_000,
            decreases len - i,
        {
            let val = base + 2 * (i as i32);
            assert(1 <= val <= 100_000) by {
                assert(val as int == base as int + 2 * i as int);
                assert(base as int + 2 * i as int <= base as int + 2 * (len as int) - 2);
            };
            nums.push(val);
            i = i + 1;
        }
        (nums, k_val)
    } else if mutation_kind == 3 {
        // Build consecutive but use k = 1
        let mut nums: Vec<i32> = Vec::new();
        let mut i: u32 = 0;
        while i < len
            invariant
                0 <= i <= len,
                nums.len() == i as int,
                1 <= len <= 500,
                1 <= base <= 100_000i32,
                base as int + len as int - 1 <= 100_000,
                forall|j: int| 0 <= j < i as int ==>
                    #[trigger] nums[j] == (base + j as i32),
                forall|j: int| 0 <= j < nums.len() ==>
                    1 <= #[trigger] nums[j] <= 100_000,
            decreases len - i,
        {
            let val = base + (i as i32);
            assert(1 <= val <= 100_000) by {
                assert(val as int == base as int + i as int);
            };
            nums.push(val);
            i = i + 1;
        }
        (nums, 1i32)
    } else if mutation_kind == 4 {
        // Build consecutive and use k = len (full array window)
        let mut nums: Vec<i32> = Vec::new();
        let mut i: u32 = 0;
        while i < len
            invariant
                0 <= i <= len,
                nums.len() == i as int,
                1 <= len <= 500,
                1 <= base <= 100_000i32,
                base as int + len as int - 1 <= 100_000,
                forall|j: int| 0 <= j < i as int ==>
                    #[trigger] nums[j] == (base + j as i32),
                forall|j: int| 0 <= j < nums.len() ==>
                    1 <= #[trigger] nums[j] <= 100_000,
            decreases len - i,
        {
            let val = base + (i as i32);
            assert(1 <= val <= 100_000) by {
                assert(val as int == base as int + i as int);
            };
            nums.push(val);
            i = i + 1;
        }
        (nums, len as i32)
    } else if mutation_kind == 5 && len >= 2 {
        // Build consecutive then break the run in the middle
        let mut nums: Vec<i32> = Vec::new();
        let mid = len / 2;
        let mut i: u32 = 0;
        while i < len
            invariant
                0 <= i <= len,
                nums.len() == i as int,
                1 <= len <= 500,
                len >= 2u32,
                mid == len / 2,
                1 <= base <= 100_000i32,
                base as int + len as int - 1 <= 100_000,
                forall|j: int| 0 <= j < nums.len() ==>
                    1 <= #[trigger] nums[j] <= 100_000,
            decreases len - i,
        {
            if i == mid {
                nums.push(base);
            } else {
                let val = base + (i as i32);
                assert(1 <= val <= 100_000) by {
                    assert(val as int == base as int + i as int);
                };
                nums.push(val);
            }
            i = i + 1;
        }
        (nums, k_val)
    } else {
        // Fallback: consecutive array
        let mut nums: Vec<i32> = Vec::new();
        let mut i: u32 = 0;
        while i < len
            invariant
                0 <= i <= len,
                nums.len() == i as int,
                1 <= len <= 500,
                1 <= base <= 100_000i32,
                base as int + len as int - 1 <= 100_000,
                forall|j: int| 0 <= j < i as int ==>
                    #[trigger] nums[j] == (base + j as i32),
                forall|j: int| 0 <= j < nums.len() ==>
                    1 <= #[trigger] nums[j] <= 100_000,
            decreases len - i,
        {
            let val = base + (i as i32);
            assert(1 <= val <= 100_000) by {
                assert(val as int == base as int + i as int);
            };
            nums.push(val);
            i = i + 1;
        }
        (nums, k_val)
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

fn build_test(base: i32, len: u32, k_val: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(base, len, k_val, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}_{}", nums, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::results_array(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1,2,3,4,3,2,5], 3),
        (vec![2,2,2,2,2], 4),
        (vec![3,2,3,2,3,2], 2),
    ];
    for (nums, k) in examples {
        emit(nums, k, &mut seen, &mut out, &mut count);
    }

    // Seeded inputs with all mutation kinds
    let bases: Vec<i32> = vec![1, 50, 100, 99_990, 1000, 5];
    let lens: Vec<u32> = vec![1, 2, 3, 5, 10, 20, 50];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    for &b in &bases {
        for &l in &lens {
            if b as i64 + l as i64 - 1 > 100_000 { continue; }
            for &mk in &mutation_kinds {
                if count >= target_count { break; }
                let k = if l == 1 { 1i32 } else { std::cmp::min(3, l as i32) };
                let (nums, k_out) = build_test(b, l, k, mk);
                emit(nums, k_out, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random test cases with diverse sizes and mutations
    while count < target_count {
        let len_class = rng.gen_range_usize(0, 4);
        let len: u32 = match len_class {
            0 => rng.gen_range_usize(1, 3) as u32,        // tiny
            1 => rng.gen_range_usize(1, 10) as u32,       // small
            2 => rng.gen_range_usize(11, 50) as u32,      // medium
            3 => rng.gen_range_usize(51, 200) as u32,     // large
            _ => rng.gen_range_usize(201, 500) as u32,    // max
        };
        let max_base = (100_001 - len as i64) as i64;
        let base = rng.gen_range_i64(1, max_base) as i32;
        let k = rng.gen_range_i64(1, len as i64) as i32;
        let mk = rng.gen_range_usize(0, 5) as u8;
        let mk_safe = if mk == 2 && (base as i64 + 2 * (len as i64) - 2 > 100_000) { 0 } else { mk };
        let (nums, k_out) = build_test(base, len, k, mk_safe);
        emit(nums, k_out, &mut seen, &mut out, &mut count);
    }
}
