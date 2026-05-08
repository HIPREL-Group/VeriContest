use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_covered(nums: Seq<Seq<i32>>, p: int, idx: int) -> bool
        decreases idx
    {
        if idx <= 0 { false }
        else {
            Self::is_covered(nums, p, idx - 1) || (nums[idx - 1][0] as int <= p && p <= nums[idx - 1][1] as int)
        }
    }

    pub open spec fn count_covered(nums: Seq<Seq<i32>>, p: int) -> int
        decreases p
    {
        if p <= 0 { 0 }
        else {
            Self::count_covered(nums, p - 1) + if Self::is_covered(nums, p, nums.len() as int) { 1int } else { 0int }
        }
    }

    pub fn number_of_points(nums: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> (#[trigger] nums.deep_view()[i]).len() == 2,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= (#[trigger] nums.deep_view()[i])[0] <= nums.deep_view()[i][1] <= 100,
        ensures
            result as int == Self::count_covered(nums.deep_view(), 100),
    {
        let ghost nums_dv = nums.deep_view();
        let mut covered = vec![false; 101];
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                covered.len() == 101,
                nums.len() <= 100,
                nums_dv == nums.deep_view(),
                forall|j: int| 0 <= j < nums.len() ==> (#[trigger] nums_dv[j]).len() == 2,
                forall|j: int| 0 <= j < nums.len() ==> 1 <= (#[trigger] nums_dv[j])[0] <= nums_dv[j][1] <= 100,
                forall|p: int| 1 <= p <= 100 ==> (#[trigger] covered@[p]) == Self::is_covered(nums_dv, p, i as int),
            decreases nums.len() - i,
        {
            proof {
                assert(nums_dv[i as int] =~= nums@[i as int]@);
                assert(nums@[i as int]@.len() == 2);
            }
            if nums[i].len() >= 2 {
                let a = nums[i][0];
                let b = nums[i][1];
                let mut l = if a <= b { a } else { b };
                let mut r = if a <= b { b } else { a };
                if l < 1 { l = 1; }
                if r > 100 { r = 100; }
                if l <= r {
                    let mut x: i32 = l;
                    while x <= r
                        invariant
                            l <= x <= r + 1,
                            covered.len() == 101,
                            1 <= l <= 100,
                            1 <= r <= 100,
                            l as int == nums_dv[i as int][0] as int,
                            r as int == nums_dv[i as int][1] as int,
                            0 <= i < nums.len(),
                            nums.len() <= 100,
                            nums_dv == nums.deep_view(),
                            forall|j: int| 0 <= j < nums.len() ==> (#[trigger] nums_dv[j]).len() == 2,
                            forall|j: int| 0 <= j < nums.len() ==> 1 <= (#[trigger] nums_dv[j])[0] <= nums_dv[j][1] <= 100,
                            forall|p: int| 1 <= p <= 100 ==> (#[trigger] covered@[p]) ==
                                (Self::is_covered(nums_dv, p, i as int) || (l as int <= p && p < x as int)),
                        decreases (r - x + 1) as int,
                    {
                        covered.set(x as usize, true);
                        x = x + 1;
                    }
                }
            }
            assert(forall|p: int| 1 <= p <= 100 ==> (#[trigger] covered@[p]) == Self::is_covered(nums_dv, p, (i + 1) as int));
            i = i + 1;
        }

        let mut ans: i32 = 0;
        i = 1;
        while i <= 100
            invariant
                1 <= i <= 101,
                covered.len() == 101,
                forall|p: int| 1 <= p <= 100 ==> (#[trigger] covered@[p]) == Self::is_covered(nums_dv, p, nums_dv.len() as int),
                ans as int == Self::count_covered(nums_dv, (i - 1) as int),
                0 <= ans <= i as i32 - 1,
                nums_dv == nums.deep_view(),
            decreases 101 - i,
        {
            if covered[i] {
                ans = ans + 1;
            }
            i = i + 1;
        }
        ans
    }
}

}
