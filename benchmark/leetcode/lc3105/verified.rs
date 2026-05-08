use vstd::prelude::*;

verus! {


pub open spec fn spec_inc(nums: Seq<i32>, i: int) -> int
    decreases i,
{
    if i <= 0 {
        1
    } else if nums[i] > nums[i - 1] {
        spec_inc(nums, i - 1) + 1
    } else {
        1
    }
}


pub open spec fn spec_dec(nums: Seq<i32>, i: int) -> int
    decreases i,
{
    if i <= 0 {
        1
    } else if nums[i] < nums[i - 1] {
        spec_dec(nums, i - 1) + 1
    } else {
        1
    }
}


pub open spec fn spec_max(a: int, b: int) -> int
{
    if a >= b { a } else { b }
}


pub open spec fn spec_best(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        1
    } else {
        spec_max(
            spec_best(nums, k - 1),
            spec_max(spec_inc(nums, k), spec_dec(nums, k)),
        )
    }
}

pub open spec fn spec_longest_monotonic_subarray(nums: Seq<i32>) -> int
{
    if nums.len() == 0 {
        0
    } else {
        spec_best(nums, (nums.len() - 1) as int)
    }
}

proof fn lemma_inc_bounds(nums: Seq<i32>, i: int)
    requires
        nums.len() > 0,
        nums.len() <= 50,
        0 <= i < nums.len() as int,
        forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 50,
    ensures
        1 <= spec_inc(nums, i) <= i + 1,
    decreases i,
{
    if i <= 0 {
    } else if nums[i] > nums[i - 1] {
        lemma_inc_bounds(nums, i - 1);
    } else {
    }
}

proof fn lemma_dec_bounds(nums: Seq<i32>, i: int)
    requires
        nums.len() > 0,
        nums.len() <= 50,
        0 <= i < nums.len() as int,
        forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 50,
    ensures
        1 <= spec_dec(nums, i) <= i + 1,
    decreases i,
{
    if i <= 0 {
    } else if nums[i] < nums[i - 1] {
        lemma_dec_bounds(nums, i - 1);
    } else {
    }
}

proof fn lemma_best_bounds(nums: Seq<i32>, k: int)
    requires
        nums.len() > 0,
        nums.len() <= 50,
        0 <= k < nums.len() as int,
        forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 50,
    ensures
        1 <= spec_best(nums, k) <= 50,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_best_bounds(nums, k - 1);
        lemma_inc_bounds(nums, k);
        lemma_dec_bounds(nums, k);
    }
}

fn longest_monotonic_subarray(nums: Vec<i32>) -> (result: i32)
    requires
        nums.len() > 0,
        nums.len() <= 50,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
    ensures
        result as int == spec_longest_monotonic_subarray(nums@),
{
    let n = nums.len();
    if n == 0 {
        return 0;
    }
    let mut best = 1i32;
    let mut inc = 1i32;
    let mut dec = 1i32;
    let mut i = 1;

    proof {
        lemma_inc_bounds(nums@, 0);
        lemma_dec_bounds(nums@, 0);
        lemma_best_bounds(nums@, 0);
    }

    while i < n
        invariant
            1 <= i <= n,
            n == nums.len(),
            n > 0,
            n <= 50,
            forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums@[j] <= 50,
            inc as int == spec_inc(nums@, (i - 1) as int),
            dec as int == spec_dec(nums@, (i - 1) as int),
            best as int == spec_best(nums@, (i - 1) as int),
            1 <= inc <= 50,
            1 <= dec <= 50,
            1 <= best <= 50,
        decreases n - i,
    {
        proof {
            lemma_inc_bounds(nums@, i as int);
            lemma_dec_bounds(nums@, i as int);
            lemma_best_bounds(nums@, i as int);
        }

        if nums[i] > nums[i - 1] {
            inc = inc + 1;
        } else {
            inc = 1;
        }
        if nums[i] < nums[i - 1] {
            dec = dec + 1;
        } else {
            dec = 1;
        }
        let cur = if inc > dec { inc } else { dec };
        if cur > best {
            best = cur;
        }
        i = i + 1;
    }
    best
}

}

fn main() {}
