use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_exp2(x: i32) -> int {
        if x == 8 {
            3
        } else if x == 4 {
            2
        } else if x == 2 || x == 6 || x == 10 {
            1
        } else {
            0
        }
    }

    pub open spec fn spec_exp3(x: i32) -> int {
        if x == 9 {
            2
        } else if x == 3 || x == 6 {
            1
        } else {
            0
        }
    }

    pub open spec fn spec_exp5(x: i32) -> int {
        if x == 5 || x == 10 { 1 } else { 0 }
    }

    pub open spec fn spec_exp7(x: i32) -> int {
        if x == 7 { 1 } else { 0 }
    }

    pub open spec fn range_sum2(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if r <= l {
            0
        } else {
            Self::range_sum2(nums, l, r - 1) + Self::spec_exp2(nums[r - 1])
        }
    }

    pub open spec fn range_min2(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if r <= l {
            4
        } else {
            let prev = Self::range_min2(nums, l, r - 1);
            let cur = Self::spec_exp2(nums[r - 1]);
            if cur < prev { cur } else { prev }
        }
    }

    pub open spec fn range_max2(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if r <= l {
            0
        } else {
            let prev = Self::range_max2(nums, l, r - 1);
            let cur = Self::spec_exp2(nums[r - 1]);
            if cur > prev { cur } else { prev }
        }
    }

    pub open spec fn range_sum3(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if r <= l {
            0
        } else {
            Self::range_sum3(nums, l, r - 1) + Self::spec_exp3(nums[r - 1])
        }
    }

    pub open spec fn range_min3(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if r <= l {
            3
        } else {
            let prev = Self::range_min3(nums, l, r - 1);
            let cur = Self::spec_exp3(nums[r - 1]);
            if cur < prev { cur } else { prev }
        }
    }

    pub open spec fn range_max3(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if r <= l {
            0
        } else {
            let prev = Self::range_max3(nums, l, r - 1);
            let cur = Self::spec_exp3(nums[r - 1]);
            if cur > prev { cur } else { prev }
        }
    }

    pub open spec fn range_sum5(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if r <= l {
            0
        } else {
            Self::range_sum5(nums, l, r - 1) + Self::spec_exp5(nums[r - 1])
        }
    }

    pub open spec fn range_min5(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if r <= l {
            2
        } else {
            let prev = Self::range_min5(nums, l, r - 1);
            let cur = Self::spec_exp5(nums[r - 1]);
            if cur < prev { cur } else { prev }
        }
    }

    pub open spec fn range_max5(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if r <= l {
            0
        } else {
            let prev = Self::range_max5(nums, l, r - 1);
            let cur = Self::spec_exp5(nums[r - 1]);
            if cur > prev { cur } else { prev }
        }
    }

    pub open spec fn range_sum7(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if r <= l {
            0
        } else {
            Self::range_sum7(nums, l, r - 1) + Self::spec_exp7(nums[r - 1])
        }
    }

    pub open spec fn range_min7(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if r <= l {
            2
        } else {
            let prev = Self::range_min7(nums, l, r - 1);
            let cur = Self::spec_exp7(nums[r - 1]);
            if cur < prev { cur } else { prev }
        }
    }

    pub open spec fn range_max7(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if r <= l {
            0
        } else {
            let prev = Self::range_max7(nums, l, r - 1);
            let cur = Self::spec_exp7(nums[r - 1]);
            if cur > prev { cur } else { prev }
        }
    }

    pub open spec fn subarray_ok(nums: Seq<i32>, l: int, r: int) -> bool {
        0 <= l < r <= nums.len()
        && Self::range_sum2(nums, l, r) == Self::range_min2(nums, l, r) + Self::range_max2(nums, l, r)
        && Self::range_sum3(nums, l, r) == Self::range_min3(nums, l, r) + Self::range_max3(nums, l, r)
        && Self::range_sum5(nums, l, r) == Self::range_min5(nums, l, r) + Self::range_max5(nums, l, r)
        && Self::range_sum7(nums, l, r) == Self::range_min7(nums, l, r) + Self::range_max7(nums, l, r)
    }

    pub open spec fn max_int(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn best_end(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if r <= l {
            0
        } else {
            Self::max_int(
                Self::best_end(nums, l, r - 1),
                if Self::subarray_ok(nums, l, r) { r - l } else { 0 },
            )
        }
    }

    pub open spec fn best_prefix(nums: Seq<i32>, i: int) -> int
        recommends
            0 <= i <= nums.len(),
        decreases i,
    {
        if i <= 0 {
            0
        } else {
            Self::max_int(
                Self::best_prefix(nums, i - 1),
                Self::best_end(nums, i - 1, nums.len() as int),
            )
        }
    }

    pub open spec fn spec_max_length(nums: Seq<i32>) -> int {
        Self::best_prefix(nums, nums.len() as int)
    }

    pub fn max_length(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10,
        ensures
            result as int == Self::spec_max_length(nums@),
    {
        let n = nums.len();
        let mut ans: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                2 <= n <= 100,
                0 <= i <= n,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 10,
                ans as int == Self::best_prefix(nums@, i as int),
            decreases n - i,
        {
            let mut sum2: i32 = 0;
            let mut min2: i32 = 4;
            let mut max2: i32 = 0;
            let mut sum3: i32 = 0;
            let mut min3: i32 = 3;
            let mut max3: i32 = 0;
            let mut sum5: i32 = 0;
            let mut min5: i32 = 2;
            let mut max5: i32 = 0;
            let mut sum7: i32 = 0;
            let mut min7: i32 = 2;
            let mut max7: i32 = 0;
            let mut best_i: i32 = 0;
            let mut j: usize = i;
            while j < n
                invariant
                    n == nums.len(),
                    2 <= n <= 100,
                    i < n,
                    i <= j <= n,
                    forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 10,
                    0 <= min2 <= 4,
                    0 <= max2 <= 3,
                    0 <= min3 <= 3,
                    0 <= max3 <= 2,
                    0 <= min5 <= 2,
                    0 <= max5 <= 1,
                    0 <= min7 <= 2,
                    0 <= max7 <= 1,
                    0 <= sum2 <= 3 * (j as int - i as int),
                    0 <= sum3 <= 2 * (j as int - i as int),
                    0 <= sum5 <= j as int - i as int,
                    0 <= sum7 <= j as int - i as int,
                    sum2 as int == Self::range_sum2(nums@, i as int, j as int),
                    min2 as int == Self::range_min2(nums@, i as int, j as int),
                    max2 as int == Self::range_max2(nums@, i as int, j as int),
                    sum3 as int == Self::range_sum3(nums@, i as int, j as int),
                    min3 as int == Self::range_min3(nums@, i as int, j as int),
                    max3 as int == Self::range_max3(nums@, i as int, j as int),
                    sum5 as int == Self::range_sum5(nums@, i as int, j as int),
                    min5 as int == Self::range_min5(nums@, i as int, j as int),
                    max5 as int == Self::range_max5(nums@, i as int, j as int),
                    sum7 as int == Self::range_sum7(nums@, i as int, j as int),
                    min7 as int == Self::range_min7(nums@, i as int, j as int),
                    max7 as int == Self::range_max7(nums@, i as int, j as int),
                    best_i as int == Self::best_end(nums@, i as int, j as int),
                decreases n - j,
            {
                let x = nums[j];
                let e2: i32 =
                    if x == 8 { 3 } else if x == 4 { 2 } else if x == 2 || x == 6 || x == 10 { 1 } else { 0 };
                let e3: i32 = if x == 9 { 2 } else if x == 3 || x == 6 { 1 } else { 0 };
                let e5: i32 = if x == 5 || x == 10 { 1 } else { 0 };
                let e7: i32 = if x == 7 { 1 } else { 0 };

                proof {
                    assert(1 <= x <= 10);
                    assert(e2 as int == Self::spec_exp2(x));
                    assert(e3 as int == Self::spec_exp3(x));
                    assert(e5 as int == Self::spec_exp5(x));
                    assert(e7 as int == Self::spec_exp7(x));
                    assert(0 <= e2 <= 3);
                    assert(0 <= e3 <= 2);
                    assert(0 <= e5 <= 1);
                    assert(0 <= e7 <= 1);
                    let ghost d: int = j as int - i as int;
                    assert(0 <= d);
                    assert(d < 100);
                    assert(0 <= sum2 + e2 <= 3 * (j as int + 1 - i as int)) by (nonlinear_arith)
                        requires
                            0 <= sum2 <= 3 * (j as int - i as int),
                            0 <= e2 <= 3,
                    {};
                    assert(0 <= sum3 + e3 <= 2 * (j as int + 1 - i as int)) by (nonlinear_arith)
                        requires
                            0 <= sum3 <= 2 * (j as int - i as int),
                            0 <= e3 <= 2,
                    {};
                    assert(0 <= sum5 + e5 <= j as int + 1 - i as int) by (nonlinear_arith)
                        requires
                            0 <= sum5 <= j as int - i as int,
                            0 <= e5 <= 1,
                    {};
                    assert(0 <= sum7 + e7 <= j as int + 1 - i as int) by (nonlinear_arith)
                        requires
                            0 <= sum7 <= j as int - i as int,
                            0 <= e7 <= 1,
                    {};
                }

                sum2 = sum2 + e2;
                if e2 < min2 {
                    min2 = e2;
                }
                if e2 > max2 {
                    max2 = e2;
                }

                sum3 = sum3 + e3;
                if e3 < min3 {
                    min3 = e3;
                }
                if e3 > max3 {
                    max3 = e3;
                }

                sum5 = sum5 + e5;
                if e5 < min5 {
                    min5 = e5;
                }
                if e5 > max5 {
                    max5 = e5;
                }

                sum7 = sum7 + e7;
                if e7 < min7 {
                    min7 = e7;
                }
                if e7 > max7 {
                    max7 = e7;
                }

                let cand: i32 =
                    if sum2 == (min2 + max2) && sum3 == (min3 + max3) && sum5 == (min5 + max5) && sum7 == (min7 + max7) {
                        (j - i + 1) as i32
                    } else {
                        0
                    };
                if cand > best_i {
                    best_i = cand;
                }

                proof {
                    assert(sum2 as int == Self::range_sum2(nums@, i as int, j as int + 1));
                    assert(min2 as int == Self::range_min2(nums@, i as int, j as int + 1));
                    assert(max2 as int == Self::range_max2(nums@, i as int, j as int + 1));
                    assert(sum3 as int == Self::range_sum3(nums@, i as int, j as int + 1));
                    assert(min3 as int == Self::range_min3(nums@, i as int, j as int + 1));
                    assert(max3 as int == Self::range_max3(nums@, i as int, j as int + 1));
                    assert(sum5 as int == Self::range_sum5(nums@, i as int, j as int + 1));
                    assert(min5 as int == Self::range_min5(nums@, i as int, j as int + 1));
                    assert(max5 as int == Self::range_max5(nums@, i as int, j as int + 1));
                    assert(sum7 as int == Self::range_sum7(nums@, i as int, j as int + 1));
                    assert(min7 as int == Self::range_min7(nums@, i as int, j as int + 1));
                    assert(max7 as int == Self::range_max7(nums@, i as int, j as int + 1));

                    assert((cand as int == j as int + 1 - i as int) == Self::subarray_ok(nums@, i as int, j as int + 1));
                    assert(best_i as int == Self::best_end(nums@, i as int, j as int + 1));
                }
                j = j + 1;
            }
            if best_i > ans {
                ans = best_i;
            }
            proof {
                assert(best_i as int == Self::best_end(nums@, i as int, n as int));
                assert(ans as int == Self::best_prefix(nums@, i as int + 1));
            }
            i = i + 1;
        }
        ans
    }
}

}
