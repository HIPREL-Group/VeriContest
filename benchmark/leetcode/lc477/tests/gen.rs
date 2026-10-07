use vstd::prelude::*;

verus! {


pub open spec fn hamming_distance_spec_helper(x: nat, acc: nat) -> nat
    decreases x,
{
    if x == 0 {
        acc
    } else {
        let ones = x % 2;
        let new_acc = acc + ones;
        hamming_distance_spec_helper(x / 2, new_acc)
    }
}

pub open spec fn hamming_distance_spec(xor_result: nat) -> nat {
    hamming_distance_spec_helper(xor_result, 0)
}

pub open spec fn total_hamming_distance_spec(nums: Seq<i32>, i: nat, j: nat, acc: nat) -> nat
    decreases nums.len() - i, nums.len() - j,
{
    if i >= nums.len() {
        acc
    } else if j >= nums.len() {
        total_hamming_distance_spec(nums, i + 1, i + 2, acc)
    } else {
        let xor_val = (nums[i as int] ^ nums[j as int]) as nat;
        let dist = hamming_distance_spec(xor_val);
        total_hamming_distance_spec(nums, i, j + 1, acc + dist)
    }
}


pub open spec fn bit_limit(k: nat) -> nat
    decreases k,
{
    if k == 0 { 1 } else { 2 * bit_limit((k - 1) as nat) }
}
proof fn popcount_bound(x: nat, acc: nat, bits: nat)
    requires x < bit_limit(bits),
    ensures hamming_distance_spec_helper(x, acc) <= acc + bits,
    decreases bits,
{
    if x > 0 {
        assert(bits > 0);
        assert(x / 2 < bit_limit((bits - 1) as nat)) by(nonlinear_arith)
            requires x < 2 * bit_limit((bits - 1) as nat);
        popcount_bound(x / 2, acc + x % 2, (bits - 1) as nat);
    }
}
proof fn total_distance_bound(nums: Seq<i32>, i: nat, j: nat, acc: nat)
    requires nums.len() <= 10000, i <= nums.len(), i + 1 <= j <= nums.len() + 1,
        i < nums.len() ==> j <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 1000000000,
    ensures total_hamming_distance_spec(nums, i, j, acc) <=
        acc + 16 * (nums.len() - i - 1) * (nums.len() - i - 2) + 32 * (nums.len() - j),
    decreases nums.len() - i, nums.len() - j,
{
    let n = nums.len() as int;
    if i >= nums.len() {
        assert(16 * (n - i - 1) * (n - i - 2) + 32 * (n - j) == 0) by(nonlinear_arith)
            requires i == n, j == n + 1;
    } else if j >= nums.len() {
        total_distance_bound(nums, i + 1, i + 2, acc);
        assert(16 * (n - (i + 1) - 1) * (n - (i + 1) - 2) + 32 * (n - (i + 2))
            <= 16 * (n - i - 1) * (n - i - 2) + 32 * (n - j)) by(nonlinear_arith)
            requires j == n;
    } else {
        let a = nums[i as int]; let b = nums[j as int];
        assert(0 <= (a ^ b) <= 2147483647) by(bit_vector)
            requires 0 <= a <= 1000000000, 0 <= b <= 1000000000;
        reveal_with_fuel(bit_limit, 32);
        popcount_bound((a ^ b) as nat, 0, 31);
        let dist = hamming_distance_spec((a ^ b) as nat);
        total_distance_bound(nums, i, j + 1, acc + dist);
    }
}
pub fn generate_test_case(raw: Vec<i32>) -> (result: Vec<i32>)
    ensures 1 <= result.len() <= 10000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000000000,
        i32::MIN <= total_hamming_distance_spec(result@, 0, 1, 0) <= i32::MAX,
{
    let n = if raw.len() == 0 { 1usize } else if raw.len() > 10000 { 10000usize } else { raw.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant i <= n, 1 <= n <= 10000, result.len() == i,
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] result[j] <= 1000000000,
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { 0 };
        result.push(if v < 0 { 0 } else if v > 1000000000 { 1000000000 } else { v });
        i += 1;
    }
    proof {
        total_distance_bound(result@, 0, 1, 0);
        assert(16 * (n - 1) * (n - 2) + 32 * (n - 1) <= 2147483647) by(nonlinear_arith)
            requires 1 <= n <= 10000;
    }
    result
}


pub struct Solution;

impl Solution {
    pub open spec fn hamming_distance_spec_helper(x: nat, acc: nat) -> nat
        decreases x,
    {
        if x == 0 {
            acc
        } else {
            let ones = x % 2;
            let new_acc = acc + ones;
            Solution::hamming_distance_spec_helper(x / 2, new_acc)
        }
    }

    pub open spec fn hamming_distance_spec(xor_result: nat) -> nat {
        Solution::hamming_distance_spec_helper(xor_result, 0)
    }

    pub open spec fn total_hamming_distance_spec(nums: Seq<i32>, i: nat, j: nat, acc: nat) -> nat
        decreases nums.len() - i, nums.len() - j,
    {
        if i >= nums.len() {
            acc
        } else if j >= nums.len() {
            Solution::total_hamming_distance_spec(nums, i + 1, i + 2, acc)
        } else {
            let xor_val = (nums[i as int] ^ nums[j as int]) as nat;
            let dist = Solution::hamming_distance_spec(xor_val);
            Solution::total_hamming_distance_spec(nums, i, j + 1, acc + dist)
        }
    }
}

// Lemma: for an array where every element equals `val`, the total hamming
// distance is zero because val ^ val == 0 for every pair.
proof fn lemma_all_same_total_zero(nums: Seq<i32>, val: i32, i: nat, j: nat, acc: nat)
    requires
        forall|k: int| 0 <= k < nums.len() ==> nums[k] == val,
        0 <= val <= i32::MAX,
    ensures
        Solution::total_hamming_distance_spec(nums, i, j, acc) == acc,
    decreases nums.len() - i, nums.len() - j,
{
    if i >= nums.len() {
        // base case: returns acc
    } else if j >= nums.len() {
        lemma_all_same_total_zero(nums, val, i + 1, i + 2, acc);
    } else {
        assert(nums[i as int] == val);
        assert(nums[j as int] == val);
        assert(val ^ val == 0i32) by(bit_vector);
        lemma_all_same_total_zero(nums, val, i, j + 1, acc);
    }
}

pub fn generate_candidate(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 10000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= i32::MAX,
        i32::MIN <= Solution::total_hamming_distance_spec(nums@, 0, 1, 0) <= i32::MAX,
    ensures
        1 <= result.len() <= 10000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= i32::MAX,
        i32::MIN <= Solution::total_hamming_distance_spec(result@, 0, 1, 0) <= i32::MAX,
{
    if mutation_kind == 0 {
        // identity — pass through
        nums
    } else if mutation_kind == 1 {
        // set every element to nums[0] (all-same ⇒ total = 0)
        let val = nums[0];
        let n = nums.len();
        let mut res: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                0 <= idx <= n,
                n == nums.len(),
                1 <= n <= 10000,
                res.len() == idx,
                0 <= val <= i32::MAX,
                forall|k: int| 0 <= k < res.len() ==> res[k] == val,
                forall|k: int| 0 <= k < res.len() ==> 0 <= #[trigger] res[k] <= i32::MAX,
            decreases n - idx,
        {
            res.push(val);
            idx += 1;
        }
        proof {
            lemma_all_same_total_zero(res@, val, 0, 1, 0);
        }
        res
    } else if mutation_kind == 2 {
        // set every element to 0 (all-same ⇒ total = 0)
        let n = nums.len();
        let mut res: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                0 <= idx <= n,
                n == nums.len(),
                1 <= n <= 10000,
                res.len() == idx,
                forall|k: int| 0 <= k < res.len() ==> res[k] == 0i32,
                forall|k: int| 0 <= k < res.len() ==> 0 <= #[trigger] res[k] <= i32::MAX,
            decreases n - idx,
        {
            res.push(0i32);
            idx += 1;
        }
        proof {
            lemma_all_same_total_zero(res@, 0i32, 0, 1, 0);
        }
        res
    } else if mutation_kind == 3 {
        // set every element to i32::MAX (all-same ⇒ total = 0)
        let n = nums.len();
        let mut res: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                0 <= idx <= n,
                n == nums.len(),
                1 <= n <= 10000,
                res.len() == idx,
                forall|k: int| 0 <= k < res.len() ==> res[k] == i32::MAX,
                forall|k: int| 0 <= k < res.len() ==> 0 <= #[trigger] res[k] <= i32::MAX,
            decreases n - idx,
        {
            res.push(i32::MAX);
            idx += 1;
        }
        proof {
            lemma_all_same_total_zero(res@, i32::MAX, 0, 1, 0);
        }
        res
    } else if mutation_kind == 4 {
        // set every element to nums[len-1] (all-same ⇒ total = 0)
        let val = nums[nums.len() - 1];
        let n = nums.len();
        let mut res: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                0 <= idx <= n,
                n == nums.len(),
                1 <= n <= 10000,
                res.len() == idx,
                0 <= val <= i32::MAX,
                forall|k: int| 0 <= k < res.len() ==> res[k] == val,
                forall|k: int| 0 <= k < res.len() ==> 0 <= #[trigger] res[k] <= i32::MAX,
            decreases n - idx,
        {
            res.push(val);
            idx += 1;
        }
        proof {
            lemma_all_same_total_zero(res@, val, 0, 1, 0);
        }
        res
    } else {
        // fallback — identity
        nums
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


include!("../code.rs");

fn random_nums(rng: &mut Rng, len: usize, lo: i64, hi: i64) -> Vec<i32> {
    (0..len).map(|_| rng.gen_range_i64(lo, hi) as i32).collect()
}

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(477);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let nums = generate_test_case(nums);
        let result = Solution::total_hamming_distance(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
        *emitted += 1;
    };

    // ---- Examples from description.md ----
    emit(vec![4, 14, 2], &mut out, &mut emitted);   // expected 6
    emit(vec![4, 14, 4], &mut out, &mut emitted);   // expected 4

    // ---- Seed arrays × mutation_kinds ----
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![0, 0],
        vec![1],
        vec![i32::MAX],
        vec![0, i32::MAX],
        vec![1, 2, 3],
        vec![0, 0, 0],
        vec![0, 1],
        vec![1, 1, 1, 1],
        vec![255, 256],
        vec![1023, 1024, 2048],
        vec![0x55555555, 0x2AAAAAAA],
        vec![100, 200, 300, 400, 500],
        vec![i32::MAX, i32::MAX, i32::MAX],
        vec![0, 1, 2, 3, 4, 5, 6, 7],
    ];

    let num_mutations: u8 = 5;
    for seed_arr in &seeds {
        for mk in 0..num_mutations {
            let result = generate_candidate(seed_arr.clone(), mk);
            emit(result, &mut out, &mut emitted);
        }
    }

    // ---- Random: diverse sizes and values ----
    while emitted < count {
        let n = match emitted % 5 {
            0 => rng.gen_range_usize(1, 3),           // tiny
            1 => rng.gen_range_usize(1, 10),           // small
            2 => rng.gen_range_usize(11, 100),         // medium
            3 => rng.gen_range_usize(101, 1000),       // large
            _ => rng.gen_range_usize(1001, 10000),     // max
        };

        let (lo, hi): (i64, i64) = match emitted % 4 {
            0 => (0, 1),                                // binary
            1 => (0, 255),                              // byte range
            2 => (0, 1_000_000_000),                    // full constraint range
            _ => (0, i32::MAX as i64),                  // full i32 range
        };

        let arr = random_nums(&mut rng, n, lo, hi);
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let result = generate_candidate(arr, mk);
        emit(result, &mut out, &mut emitted);
    }
}
