use vstd::prelude::*;

verus! {




pub open spec fn spec_run(nums: Seq<i32>, i: int) -> int
    decreases i,
{
    if i < 2 {
        0
    } else if nums[i] - nums[i - 1] == nums[i - 1] - nums[i - 2] {
        spec_run(nums, i - 1) + 1
    } else {
        0
    }
}


pub open spec fn spec_total(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k < 2 {
        0
    } else {
        spec_total(nums, k - 1) + spec_run(nums, k)
    }
}

pub open spec fn spec_number_of_arithmetic_slices(nums: Seq<i32>) -> int
{
    if nums.len() < 3 {
        0
    } else {
        spec_total(nums, (nums.len() - 1) as int)
    }
}


proof fn lemma_run_bounds(nums: Seq<i32>, i: int)
    requires
        0 <= i < nums.len(),
        nums.len() <= 5000,
        forall|j: int| 0 <= j < nums.len() ==> -1000 <= #[trigger] nums[j] <= 1000,
    ensures
        0 <= spec_run(nums, i),
        spec_run(nums, i) <= if i < 2 { 0int } else { i - 1 },
    decreases i,
{
    if i < 2 {
    } else if nums[i] - nums[i - 1] == nums[i - 1] - nums[i - 2] {
        lemma_run_bounds(nums, i - 1);
    } else {
    }
}



proof fn lemma_total_bounds(nums: Seq<i32>, k: int)
    requires
        0 <= k < nums.len(),
        nums.len() <= 5000,
        forall|j: int| 0 <= j < nums.len() ==> -1000 <= #[trigger] nums[j] <= 1000,
    ensures
        0 <= spec_total(nums, k),
        spec_total(nums, k) <= k * k,
    decreases k,
{
    if k < 2 {
    } else {
        lemma_total_bounds(nums, k - 1);
        lemma_run_bounds(nums, k);
        
        
        
        
        assert(spec_total(nums, k) <= (k - 1) * (k - 1) + (k - 1)) by (nonlinear_arith)
            requires
                spec_total(nums, k - 1) <= (k - 1) * (k - 1),
                spec_run(nums, k) <= k - 1,
                spec_total(nums, k) == spec_total(nums, k - 1) + spec_run(nums, k),
        {
        };
        assert((k - 1) * (k - 1) + (k - 1) <= k * k) by (nonlinear_arith)
            requires
                k >= 2,
        {
        };
    }
}

fn number_of_arithmetic_slices(nums: Vec<i32>) -> (result: i32)
    requires
        nums.len() >= 1,
        nums.len() <= 5000,
        forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
    ensures
        result as int == spec_number_of_arithmetic_slices(nums@),
{
    let n = nums.len();
    if n < 3 {
        return 0;
    }
    let mut total = 0i32;
    let mut curr = 0i32;
    let mut i = 2;

    while i < n
        invariant
            2 <= i <= n,
            n == nums.len(),
            n >= 3,
            n <= 5000,
            forall|j: int| 0 <= j < nums.len() ==> -1000 <= #[trigger] nums@[j] <= 1000,
            curr as int == spec_run(nums@, (i - 1) as int),
            total as int == spec_total(nums@, (i - 1) as int),
            0 <= curr,
            curr as int <= (i - 2) as int,
            0 <= total,
            total as int <= ((i - 1) * (i - 1)) as int,
        decreases n - i,
    {
        proof {
            lemma_run_bounds(nums@, i as int);
            lemma_total_bounds(nums@, i as int);
        }

        if nums[i] - nums[i - 1] == nums[i - 1] - nums[i - 2] {
            curr = curr + 1;
            assert(total as int + curr as int <= i * i) by (nonlinear_arith)
                requires
                    total as int <= ((i - 1) * (i - 1)) as int,
                    curr as int <= (i - 1) as int,
                    i >= 2,
            {
            };
            assert(i * i <= 5000 * 5000) by (nonlinear_arith)
                requires i <= 5000i64,
            {
            };
            assert(total as int + curr as int <= 25_000_000);
            total = total + curr;
        } else {
            curr = 0;
        }
        i = i + 1;
    }
    total
}

}

fn main() {}
