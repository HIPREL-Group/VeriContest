use vstd::prelude::*;

verus! {


    pub open spec fn contribution(nums: Seq<i32>, target: nat, idx: nat) -> int
        decreases target, idx,
    {
        if idx < nums.len() as nat && 0 < nums[idx as int] as int <= target as int {
            combination_count(nums, ((target as int) - nums[idx as int] as int) as nat)
        } else {
            0
        }
    }

    pub open spec fn prefix_count(nums: Seq<i32>, target: nat, end: nat) -> int
        decreases target, end,
    {
        if end == 0 {
            0
        } else {
            prefix_count(nums, target, (end - 1) as nat)
                + contribution(nums, target, (end - 1) as nat)
        }
    }

    pub open spec fn combination_count(nums: Seq<i32>, target: nat) -> int
        decreases target,
    {
        if target == 0 {
            1
        } else {
            prefix_count(nums, target, nums.len() as nat)
        }
    }


fn bounded_target(nums: &Vec<i32>, target: i32) -> (result: i32)
    requires 1 <= nums.len() <= 200, 1 <= target <= 1000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
    ensures 1 <= result <= target, combination_count(nums@, result as nat) <= i32::MAX,
{
    let mut dp: Vec<i64> = Vec::new();
    dp.push(1);
    let mut t = 1usize;
    while t <= target as usize
        invariant 1 <= t <= target + 1, 1 <= target <= 1000, 1 <= nums.len() <= 200,
            dp.len() == t, dp[0] == 1,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            forall|i: int| 0 <= i < t ==> 0 <= #[trigger] dp[i] <= i32::MAX,
            forall|i: int| 0 <= i < t ==> #[trigger] dp[i] == combination_count(nums@, i as nat),
        decreases target + 1 - t,
    {
        let mut sum = 0i64;
        let mut j = 0usize;
        while j < nums.len()
            invariant j <= nums.len() <= 200, 1 <= t <= target <= 1000,
                dp.len() == t, dp[0] == 1,
                forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
                forall|i: int| 0 <= i < t ==> 0 <= #[trigger] dp[i] <= i32::MAX,
                forall|i: int| 0 <= i < t ==> #[trigger] dp[i] == combination_count(nums@, i as nat),
                0 <= sum <= j * 2147483647,
                sum == prefix_count(nums@, t as nat, j as nat),
                t == 1 ==> sum <= j,
            decreases nums.len() - j,
        {
            let add = if nums[j] as usize <= t {
                let k = t - nums[j] as usize;
                assert(dp[k as int] == combination_count(nums@, k as nat));
                dp[k]
            } else { 0 };
            assert(add == contribution(nums@, t as nat, j as nat));
            sum += add;
            j += 1;
        }
        if sum > 2147483647 {
            assert(t > 1);
            assert(dp[t as int - 1] == combination_count(nums@, (t - 1) as nat));
            return (t - 1) as i32;
        }
        dp.push(sum);
        t += 1;
    }
    assert(dp[target as int] == combination_count(nums@, target as nat));
    target
}
pub fn generate_test_case(raw: Vec<i32>, target: i32) -> (result: (Vec<i32>, i32))
    ensures 1 <= result.0.len() <= 200,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] != result.0[j],
        1 <= result.1 <= 1000, combination_count(result.0@, result.1 as nat) <= i32::MAX,
{
    let end = if raw.len() > 200 { 200usize } else { raw.len() };
    let mut nums: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < end
        invariant i <= end <= raw.len(), end <= 200, nums.len() <= i,
            forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1000,
            forall|j: int, k: int| 0 <= j < k < nums.len() ==> nums[j] != nums[k],
        decreases end - i,
    {
        let v = raw[i];
        let v = if v < 1 { 1 } else if v > 1000 { 1000 } else { v };
        let mut found = false;
        let mut j = 0usize;
        while j < nums.len()
            invariant j <= nums.len(),
                !found ==> forall|k: int| 0 <= k < j ==> #[trigger] nums[k] != v,
            decreases nums.len() - j,
        { if nums[j] == v { found = true; } j += 1; }
        if !found { nums.push(v); }
        i += 1;
    }
    if nums.len() == 0 { nums.push(1); }
    let target = if target < 1 { 1 } else if target > 1000 { 1000 } else { target };
    let target = bounded_target(&nums, target);
    (nums, target)
}


pub struct Solution;

impl Solution {
    // ---- spec fn helpers copied from spec.rs ----

    pub open spec fn contribution(nums: Seq<i32>, target: nat, idx: nat) -> int
        decreases target, idx,
    {
        if idx < nums.len() as nat && 0 < nums[idx as int] as int <= target as int {
            Self::combination_count(nums, ((target as int) - nums[idx as int] as int) as nat)
        } else {
            0
        }
    }

    pub open spec fn prefix_count(nums: Seq<i32>, target: nat, end: nat) -> int
        decreases target, end,
    {
        if end == 0 {
            0
        } else {
            Self::prefix_count(nums, target, (end - 1) as nat)
                + Self::contribution(nums, target, (end - 1) as nat)
        }
    }

    pub open spec fn combination_count(nums: Seq<i32>, target: nat) -> int
        decreases target,
    {
        if target == 0 {
            1
        } else {
            Self::prefix_count(nums, target, nums.len() as nat)
        }
    }

    // ---- proof lemma ----

    /// When every element of `nums` exceeds `bound`, prefix_count is zero
    /// for any positive target at most `bound`.
    proof fn lemma_prefix_count_zero(nums: Seq<i32>, bound: int, t: nat, end: nat)
        requires
            t > 0,
            t as int <= bound,
            end <= nums.len() as nat,
            forall|i: int| 0 <= i < nums.len() ==> nums[i] as int > bound,
        ensures
            Self::prefix_count(nums, t, end) == 0,
        decreases end,
    {
        if end > 0 {
            Self::lemma_prefix_count_zero(nums, bound, t, (end - 1) as nat);
            let idx = (end - 1) as nat;
            assert(idx < nums.len() as nat);
            assert(nums[idx as int] as int > bound);
            assert(nums[idx as int] as int > t as int);
            // The condition in contribution: 0 < nums[idx] <= t is false
            // because nums[idx] > t, so contribution == 0
            assert(!(nums[idx as int] as int <= t as int));
            assert(Self::contribution(nums, t, idx) == 0);
        }
    }

    // ---- verified generator ----

    /// Builds a distinct array of consecutive integers [base, base+1, …, base+count-1]
    /// where every element exceeds target, guaranteeing combination_count ≤ i32::MAX
    /// for all sub-targets 0..=target.  Mutations only decrease the target.
    pub fn generate_candidate(
        base: i32,
        count: usize,
        target: i32,
        mutation_kind: u8,
    ) -> (result: (Vec<i32>, i32))
        requires
            1 <= count <= 200,
            1 <= target <= 999,
            target < base,
            1 <= base,
            base as int + count as int - 1 <= 1000,
        ensures
            1 <= result.0.len() <= 200,
            forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
            forall |i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] != result.0[j],
            1 <= result.1 <= 1000,
            forall |t: int| 0 <= t <= result.1 as int ==> #[trigger] Self::combination_count(result.0@, t as nat) <= i32::MAX,
    {
        // Build nums = [base, base+1, …, base+count-1]
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < count
            invariant
                0 <= i <= count,
                nums.len() == i,
                1 <= count <= 200,
                1 <= target <= 999,
                target < base,
                1 <= base,
                base as int + count as int - 1 <= 1000,
                forall|k: int| 0 <= k < i as int ==> nums[k] as int == base as int + k,
                forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000,
                forall|k: int| 0 <= k < nums.len() ==> nums[k] as int > target as int,
                forall|k: int, l: int| 0 <= k < l < nums.len() ==> nums[k] != nums[l],
            decreases count - i,
        {
            let val = base + i as i32;

            proof {
                assert(val as int == base as int + i as int);
                assert(1 <= val);
                assert(val as int <= base as int + count as int - 1);
                assert(val <= 1000);
                assert(val as int > target as int);

                assert forall|k: int| 0 <= k < nums.len() implies nums[k] != val by {
                    assert(nums[k] as int == base as int + k);
                    assert(val as int == base as int + i as int);
                    assert(k < i as int);
                };
            }

            nums.push(val);
            i = i + 1;
        }

        // Apply target mutation — only decrease or keep same
        let mt: i32 = if mutation_kind == 1 && target > 1 {
            (target - 1) as i32
        } else if mutation_kind == 2 {
            1i32
        } else if mutation_kind == 3 && target >= 4 {
            target / 2
        } else {
            target
        };

        proof {
            assert(1 <= mt <= target);
            assert(mt as int <= target as int);
            assert(forall|k: int| 0 <= k < nums.len() ==> nums[k] as int > target as int);
            assert(forall|k: int| 0 <= k < nums.len() ==> nums[k] as int > mt as int);

            assert forall|t: int| 0 <= t <= mt as int
                implies (#[trigger] Self::combination_count(nums@, t as nat) <= i32::MAX) by {
                if t == 0 {
                    // combination_count(nums@, 0) = 1 <= i32::MAX
                } else {
                    Self::lemma_prefix_count_zero(nums@, mt as int, t as nat, nums.len() as nat);
                    // prefix_count == 0, so combination_count == 0 <= i32::MAX
                }
            };
        }

        (nums, mt)
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

include!("../code.rs");

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

fn main() {
    use std::io::Write;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count: usize = 0;

    macro_rules! emit_gen {
        ($base:expr, $cnt:expr, $target:expr, $mk:expr) => {{
            let (nums, target) = Solution::generate_candidate($base, $cnt, $target, $mk);
            let (nums, target) = generate_test_case(nums, target);
            let output = Solution::combination_sum4(nums.clone(), target);
            writeln!(out, "{}", json!({
                "input": {"nums": nums, "target": target},
                "output": output
            })).unwrap();
            count += 1;
        }};
    }

    macro_rules! emit_raw {
        ($nums:expr, $target:expr) => {{
            let nums: Vec<i32> = $nums;
            let target: i32 = $target;
            let (nums, target) = generate_test_case(nums, target);
            let output = Solution::combination_sum4(nums.clone(), target);
            writeln!(out, "{}", json!({
                "input": {"nums": nums, "target": target},
                "output": output
            })).unwrap();
            count += 1;
        }};
    }

    // ---- Description examples (raw — elements may be ≤ target) ----
    emit_raw!(vec![1, 2, 3], 4);   // answer = 7
    emit_raw!(vec![9], 3);         // answer = 0

    // ---- Additional non-trivial raw examples ----
    emit_raw!(vec![1], 1);
    emit_raw!(vec![1], 10);
    emit_raw!(vec![2], 4);
    emit_raw!(vec![3], 9);
    emit_raw!(vec![1, 2], 4);
    emit_raw!(vec![1, 3], 5);
    emit_raw!(vec![4, 2, 1], 32);
    emit_raw!(vec![3, 1, 2], 4);

    // ---- Single element, all mutations ----
    for mk in 0u8..=3 {
        emit_gen!(10, 1, 5, mk);
        emit_gen!(1000, 1, 999, mk);
        emit_gen!(2, 1, 1, mk);
        emit_gen!(501, 1, 500, mk);
    }

    // ---- Small arrays (2-5 elements), all mutations ----
    for mk in 0u8..=3 {
        emit_gen!(100, 5, 99, mk);
        emit_gen!(996, 5, 50, mk);
        emit_gen!(2, 3, 1, mk);
        emit_gen!(500, 2, 499, mk);
    }

    // ---- Medium arrays (10-50 elements) ----
    for mk in 0u8..=3 {
        emit_gen!(11, 10, 10, mk);
        emit_gen!(51, 50, 50, mk);
        emit_gen!(901, 100, 50, mk);
    }

    // ---- Large arrays (100-200 elements) ----
    for mk in [0u8, 1, 2] {
        emit_gen!(2, 200, 1, mk);
        emit_gen!(801, 200, 100, mk);
    }

    // ---- Boundary cases ----
    emit_gen!(2, 200, 1, 0);
    emit_gen!(501, 200, 500, 0);
    emit_gen!(1000, 1, 999, 0);
    emit_gen!(3, 100, 2, 0);
    emit_gen!(2, 1, 1, 0);
    emit_gen!(1000, 1, 1, 0);

    // ---- Fill remaining with random configurations ----
    while count < goal {
        let target = rng.gen_range_i64(1, 999) as i32;
        let min_base = target as i64 + 1;
        if min_base > 1000 {
            continue;
        }
        let base = rng.gen_range_i64(min_base, 1000) as i32;
        let max_count = std::cmp::min(200, (1000 - base as i64 + 1) as usize);
        if max_count < 1 {
            continue;
        }
        let cnt = match count % 5 {
            0 => 1,
            1 => rng.gen_range_usize(1, std::cmp::min(5, max_count)),
            2 => rng.gen_range_usize(1, std::cmp::min(20, max_count)),
            3 => rng.gen_range_usize(1, std::cmp::min(100, max_count)),
            _ => rng.gen_range_usize(1, max_count),
        };
        let mk = rng.gen_range_usize(0, 3) as u8;
        emit_gen!(base, cnt, target, mk);
    }
}
