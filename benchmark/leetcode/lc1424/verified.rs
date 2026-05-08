use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_diag_val(nums: Seq<Vec<i32>>, i: int) -> int
        decreases nums.len() - i
    {
        if i >= nums.len() {
            0int
        } else {
            let d = i + nums[i].len() - 1;
            let rest = Self::max_diag_val(nums, i + 1);
            if d > rest { d } else { rest }
        }
    }

    pub open spec fn diag_seg(nums: Seq<Vec<i32>>, d: int, hi: int, lo: int) -> Seq<i32>
        decreases (if hi >= lo && hi >= 0 { hi - lo + 1 } else { 0 }) as nat
    {
        if hi < lo || hi < 0 {
            Seq::<i32>::empty()
        } else {
            let j = d - hi;
            let head = if hi < nums.len() && 0 <= j && j < nums[hi].len() {
                seq![nums[hi][j]]
            } else {
                Seq::<i32>::empty()
            };
            head + Self::diag_seg(nums, d, hi - 1, lo)
        }
    }

    pub open spec fn diag_order(nums: Seq<Vec<i32>>, max_d: int) -> Seq<i32>
        decreases (if max_d >= 0 { max_d + 1 } else { 0 }) as nat
    {
        if max_d < 0 {
            Seq::<i32>::empty()
        } else {
            let m = nums.len() as int;
            let start_i = if max_d < m { max_d } else { m - 1 };
            Self::diag_order(nums, max_d - 1) + Self::diag_seg(nums, max_d, start_i, 0)
        }
    }

    proof fn max_diag_bound(nums: Seq<Vec<i32>>, i: int)
        requires
            0 <= i <= nums.len(),
            forall |k: int| 0 <= k < nums.len() ==>
                1 <= (#[trigger] nums[k]).len() <= 100000,
            nums.len() <= 100000,
        ensures
            Self::max_diag_val(nums, i) <= 199999,
            Self::max_diag_val(nums, i) >= 0,
        decreases nums.len() - i,
    {
        if i >= nums.len() {
        } else {
            Self::max_diag_bound(nums, i + 1);
        }
    }

    proof fn diag_seg_extend(nums: Seq<Vec<i32>>, d: int, hi: int, lo: int)
        requires
            lo >= 1,
            hi >= lo - 1,
        ensures
            Self::diag_seg(nums, d, hi, lo - 1) =~=
                if (lo - 1) < nums.len() && 0 <= d - (lo - 1) && d - (lo - 1) < nums[lo - 1].len()
                { Self::diag_seg(nums, d, hi, lo).push(nums[lo - 1][(d - (lo - 1))]) }
                else { Self::diag_seg(nums, d, hi, lo) },
        decreases hi - lo + 2,
    {
        if hi == lo - 1 {
            assert(Self::diag_seg(nums, d, hi, lo) =~= Seq::<i32>::empty());
            assert(Self::diag_seg(nums, d, lo - 2, lo - 1) =~= Seq::<i32>::empty());
        } else {
            Self::diag_seg_extend(nums, d, hi - 1, lo);
        }
    }

    pub fn find_diagonal_order(nums: Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            1 <= nums@.len() <= 100000,
            forall |i: int| 0 <= i < nums@.len() ==>
                1 <= (#[trigger] nums@[i]).len() <= 100000,
            forall |i: int, j: int| 0 <= i < nums@.len() && 0 <= j < nums@[i].len() ==>
                1 <= (#[trigger] nums@[i][j]) <= 100000,
        ensures
            result@ == Self::diag_order(nums@, Self::max_diag_val(nums@, 0)),
    {
        let m = nums.len();

        let mut max_d: usize = 0;
        let mut i: usize = m;
        while i > 0
            invariant
                0 <= i <= m,
                m == nums.len(),
                m <= 100000,
                forall |k: int| 0 <= k < nums@.len() ==>
                    1 <= (#[trigger] nums@[k]).len() <= 100000,
                max_d as int == Self::max_diag_val(nums@, i as int),
                max_d <= 199999,
            decreases i,
        {
            i = i - 1;
            proof {
                Self::max_diag_bound(nums@, i as int + 1);
            }
            let d = i + nums[i].len() - 1;
            if d > max_d {
                max_d = d;
            }
        }

        let mut result: Vec<i32> = Vec::new();
        let mut d: usize = 0;
        while d <= max_d
            invariant
                0 <= d <= max_d + 1,
                m == nums.len(),
                m >= 1,
                m <= 100000,
                max_d <= 199999,
                max_d as int == Self::max_diag_val(nums@, 0),
                forall |k: int| 0 <= k < nums@.len() ==>
                    1 <= (#[trigger] nums@[k]).len() <= 100000,
                result@ =~= Self::diag_order(nums@, d as int - 1),
            decreases max_d - d + 1,
        {
            let start_i: usize = if d < m { d } else { m - 1 };
            let ghost pre_diag = result@;
            let mut ci: usize = start_i + 1;

            while ci > 0
                invariant
                    0 <= ci <= start_i + 1,
                    start_i < m,
                    d <= max_d,
                    m == nums.len(),
                    start_i as int == (if (d as int) < (m as int) { d as int } else { m as int - 1 }),
                    forall |k: int| 0 <= k < nums@.len() ==>
                        1 <= (#[trigger] nums@[k]).len() <= 100000,
                    pre_diag =~= Self::diag_order(nums@, d as int - 1),
                    result@ =~= pre_diag + Self::diag_seg(nums@, d as int, start_i as int, ci as int),
                decreases ci,
            {
                ci = ci - 1;

                proof {
                    Self::diag_seg_extend(nums@, d as int, start_i as int, ci as int + 1);
                }

                if d - ci < nums[ci].len() {
                    result.push(nums[ci][d - ci]);
                    assert(result@ =~= pre_diag + Self::diag_seg(nums@, d as int, start_i as int, ci as int + 1).push(nums@[ci as int][(d - ci) as int]));
                }
            }

            proof {
                assert(result@ =~= pre_diag + Self::diag_seg(nums@, d as int, start_i as int, 0));
            }

            d = d + 1;
        }
        result
    }
}

}
