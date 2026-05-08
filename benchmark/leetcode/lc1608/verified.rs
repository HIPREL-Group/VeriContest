use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_geq(nums: Seq<i32>, x: int) -> int
    decreases nums.len()
{
    if nums.len() == 0 {
        0
    } else if nums.last() >= x {
        1 + count_geq(nums.drop_last(), x)
    } else {
        count_geq(nums.drop_last(), x)
    }
}

proof fn lemma_count_geq_bounded(nums: Seq<i32>, x: int)
    ensures 0 <= count_geq(nums, x) <= nums.len()
    decreases nums.len()
{
    if nums.len() > 0 {
        lemma_count_geq_bounded(nums.drop_last(), x);
    }
}

proof fn lemma_count_geq_step(nums: Seq<i32>, x: int, j: int)
    requires 0 <= j < nums.len()
    ensures
        count_geq(nums.subrange(0, j + 1), x) ==
            count_geq(nums.subrange(0, j), x) + if nums[j] >= x { 1int } else { 0int }
{
    let s = nums.subrange(0, j + 1);
    assert(s.last() == nums[j]);
    assert(s.drop_last() =~= nums.subrange(0, j));
}

impl Solution {
    pub fn special_array(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
        ensures
            result == -1 || 1 <= result <= nums.len(),
            result >= 0 ==> count_geq(nums@, result as int) == result as int,
            result == -1 ==> forall |x: int| 1 <= x <= nums.len() ==> count_geq(nums@, x) != x,
    {
        let n = nums.len() as i32;
        let mut x = 1;
        while x <= n
            invariant
                1 <= x <= n + 1,
                n == nums.len() as i32,
                1 <= nums.len() <= 100,
                forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
                forall |y: int| 1 <= y < x as int ==> count_geq(nums@, y) != y,
            decreases n - x + 1,
        {
            let mut count = 0;
            let mut j: usize = 0;
            while j < nums.len()
                invariant
                    0 <= j <= nums.len(),
                    1 <= x <= n,
                    n == nums.len() as i32,
                    1 <= nums.len() <= 100,
                    forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
                    0 <= count <= j,
                    count as int == count_geq(nums@.subrange(0, j as int), x as int),
                    forall |y: int| 1 <= y < x as int ==> count_geq(nums@, y) != y,
                decreases nums.len() - j,
            {
                proof {
                    lemma_count_geq_step(nums@, x as int, j as int);
                    lemma_count_geq_bounded(nums@.subrange(0, (j + 1) as int), x as int);
                }
                if nums[j] >= x {
                    count = count + 1;
                }
                j = j + 1;
            }
            proof {
                assert(nums@.subrange(0, nums@.len() as int) =~= nums@);
            }
            if count == x {
                return x;
            }
            x = x + 1;
        }
        -1
    }
}

}
