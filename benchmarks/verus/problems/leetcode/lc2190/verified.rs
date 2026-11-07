use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_following(nums: Seq<i32>, key: i32, target: i32, end: int) -> int
        recommends
            0 <= end <= nums.len(),
        decreases end,
    {
        if end <= 1 {
            0
        } else {
            Self::count_following(nums, key, target, end - 1)
                + if nums[end - 2] == key && nums[end - 1] == target { 1int } else { 0int }
        }
    }

    pub open spec fn all_followers_leq_target(nums: Seq<i32>, key: i32, n: int, target: int) -> bool {
        Self::count_following(nums, key, key, n) <= Self::count_following(nums, key, target as i32, n)
            && (forall |t: int| 1 <= t <= 1000 ==>
                #[trigger] Self::count_following(nums, key, t as i32, n)
                    <= Self::count_following(nums, key, target as i32, n))
    }

    pub fn most_frequent(nums: Vec<i32>, key: i32) -> (result: i32)
        requires
            2 <= nums.len() <= 1000,
            1 <= key <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            exists |i: int| 0 <= i < nums.len() - 1 && nums[i] == key,
            forall |t1: int, t2: int|
                1 <= t1 <= 1000 && 1 <= t2 <= 1000
                    && #[trigger] Self::all_followers_leq_target(nums@, key, nums.len() as int, t1)
                    && #[trigger] Self::all_followers_leq_target(nums@, key, nums.len() as int, t2)
                    ==> t1 == t2,
        ensures
            1 <= result <= 1000,
            forall |t: int| 1 <= t <= 1000 ==> #[trigger] Self::count_following(nums@, key, t as i32, nums.len() as int)
                <= Self::count_following(nums@, key, result, nums.len() as int),
    {
        let n: usize = nums.len();
        let mut best_target: i32 = 1;
        let mut best_count: usize = 0;

        let mut cnt0: usize = 0;
        let mut j0: usize = 1;
        while j0 < n
            invariant
                n == nums.len(),
                2 <= n <= 1000,
                1 <= key <= 1000,
                forall |i: int| 0 <= i < n ==> 1 <= #[trigger] nums[i] <= 1000,
                1 <= j0 <= n,
                0 <= cnt0 <= j0 - 1,
                cnt0 as int == Self::count_following(nums@, key, 1, j0 as int),
            decreases n - j0,
        {
            if nums[j0 - 1] == key && nums[j0] == 1 {
                cnt0 = cnt0 + 1;
            }
            j0 = j0 + 1;
            proof {
                assert(Self::count_following(nums@, key, 1, j0 as int)
                    == Self::count_following(nums@, key, 1, (j0 - 1) as int)
                        + if nums[(j0 - 1) as int - 1] == key && nums[(j0 - 1) as int] == 1 { 1int } else { 0int });
            }
        }
        best_count = cnt0;

        let mut target: i32 = 2;
        while target <= 1000
            invariant
                n == nums.len(),
                2 <= n <= 1000,
                1 <= key <= 1000,
                forall |i: int| 0 <= i < n ==> 1 <= #[trigger] nums[i] <= 1000,
                2 <= target <= 1001,
                1 <= best_target <= 1000,
                0 <= best_count <= 1000,
                best_count as int == Self::count_following(nums@, key, best_target, n as int),
                forall |t: int| 1 <= t < target ==> #[trigger] Self::count_following(nums@, key, t as i32, n as int) <= best_count as int,
            decreases 1001 - target,
        {
            let mut cnt: usize = 0;
            let mut j: usize = 1;
            while j < n
                invariant
                    n == nums.len(),
                    2 <= n <= 1000,
                    1 <= key <= 1000,
                    1 <= target <= 1000,
                    1 <= j <= n,
                    0 <= cnt <= j - 1,
                    cnt as int == Self::count_following(nums@, key, target, j as int),
                decreases n - j,
            {
                if nums[j - 1] == key && nums[j] == target {
                    cnt = cnt + 1;
                }
                j = j + 1;
                proof {
                    assert(Self::count_following(nums@, key, target, j as int)
                        == Self::count_following(nums@, key, target, (j - 1) as int)
                            + if nums[(j - 1) as int - 1] == key && nums[(j - 1) as int] == target { 1int } else { 0int });
                }
            }

            let prev_best_count: usize = best_count;
            let prev_best_target: i32 = best_target;
            if cnt > best_count {
                best_count = cnt;
                best_target = target;
            }
            proof {
                assert(cnt as int == Self::count_following(nums@, key, target, n as int));
                assert forall |u: int| 1 <= u && u < target + 1 implies #[trigger] Self::count_following(nums@, key, u as i32, n as int) <= best_count as int by {
                    if u < target {
                        assert(Self::count_following(nums@, key, u as i32, n as int) <= prev_best_count as int);
                        assert(prev_best_count as int <= best_count as int);
                    } else {
                        assert(u == target);
                        if cnt > prev_best_count {
                            assert(best_count == cnt);
                        } else {
                            assert(best_count == prev_best_count);
                            assert(cnt <= best_count);
                        }
                    }
                };
                if cnt > prev_best_count {
                    assert(best_count == cnt);
                    assert(best_target == target);
                    assert(best_count as int == Self::count_following(nums@, key, best_target, n as int));
                } else {
                    assert(best_count == prev_best_count);
                    assert(best_target == prev_best_target);
                    assert(best_count as int == Self::count_following(nums@, key, best_target, n as int));
                }
            }
            target = target + 1;
        }

        proof {
            assert(forall |t: int| 1 <= t <= 1000 ==> #[trigger] Self::count_following(nums@, key, t as i32, n as int)
                <= Self::count_following(nums@, key, best_target, n as int));
        }

        best_target
    }
}

}
