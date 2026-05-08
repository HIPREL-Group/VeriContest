use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_sorted_range(s: Seq<i32>, lo: int, hi: int) -> bool {
        forall |i: int, j: int| lo <= i < j < hi ==> s[i] <= s[j]
    }

    pub open spec fn can_sort_by_right_shifts(s: Seq<i32>, k: int) -> bool {
        let n = s.len() as int;
        let p = n - k;
        0 <= k <= n - 1
        && Self::is_sorted_range(s, p, n)
        && Self::is_sorted_range(s, 0, p)
        && (k > 0 ==> s[n - 1] <= s[0])
    }

    pub fn minimum_right_shifts(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
        ensures
            -1 <= result,
            result < nums.len() as i32,
            result >= 0 ==> Self::can_sort_by_right_shifts(nums@, result as int),
            result == -1 ==> forall |k: int| 0 <= k < nums.len() ==> !Self::can_sort_by_right_shifts(nums@, k),
    {
        let n = nums.len();
        let mut break_count: usize = 0;
        let mut break_pos: usize = 0;
        let mut i: usize = 0;

        while i + 1 < n
            invariant
                0 <= i <= n - 1,
                n == nums.len(),
                1 <= n <= 100,
                forall |k: int| 0 <= k < n ==> 1 <= #[trigger] nums[k] <= 100,
                forall |k: int, l: int| 0 <= k < l < n ==> nums[k] != nums[l],
                0 <= break_pos < n,
                break_count <= i,
                break_count == 0 ==> Self::is_sorted_range(nums@, 0, (i + 1) as int),
                break_count >= 1 ==> (
                    break_pos < i
                    && nums[break_pos as int] > nums[(break_pos + 1) as int]
                    && Self::is_sorted_range(nums@, 0, (break_pos + 1) as int)
                ),
                break_count == 1 ==> Self::is_sorted_range(nums@, (break_pos + 1) as int, (i + 1) as int),
                break_count >= 2 ==> (exists |j: int| j > break_pos as int && j < i as int && #[trigger] nums[j] > nums[j + 1]),
            decreases n - 1 - i,
        {
            if nums[i] > nums[i + 1] {
                if break_count == 0 {
                    break_pos = i;
                } else if break_count == 1 {
                    proof {
                        assert((break_pos as int) < (i as int));
                        assert(nums@[i as int] > nums@[(i + 1) as int]);
                    }
                }
                break_count = break_count + 1;
            } else {
                proof {
                    if break_count == 0 {
                        assert forall |a: int, b: int| 0 <= a < b < (i + 2) as int implies nums@[a] <= nums@[b] by {
                            if b == (i + 1) as int && a < i as int {
                                assert(nums@[a] <= nums@[i as int]);
                            }
                        };
                    }
                    if break_count == 1 {
                        assert forall |a: int, b: int| (break_pos + 1) as int <= a < b < (i + 2) as int implies nums@[a] <= nums@[b] by {
                            if b == (i + 1) as int && a < i as int {
                                assert(nums@[a] <= nums@[i as int]);
                            }
                        };
                    }
                }
            }
            i = i + 1;
        }

        if break_count == 0 {
            proof {
                assert(Self::can_sort_by_right_shifts(nums@, 0));
            }
            return 0;
        }

        if break_count >= 2 {
            proof {
                let ghost j2 = choose |j: int| j > (break_pos as int) && j < (n as int - 1) && #[trigger] nums@[j] > nums@[j + 1];
                assert(j2 > (break_pos as int) && j2 < n as int - 1 && nums@[j2] > nums@[j2 + 1]);
                assert forall |k: int| 0 <= k < n as int implies !Self::can_sort_by_right_shifts(nums@, k) by {
                    let p = n as int - k;
                    if k == 0 {
                        assert(nums@[break_pos as int] > nums@[(break_pos + 1) as int]);
                    } else if (break_pos as int) + 1 < p {
                        assert(nums@[break_pos as int] > nums@[(break_pos + 1) as int]);
                    } else {
                        assert(j2 >= p);
                        assert(j2 + 1 < n as int);
                        assert(nums@[j2] > nums@[j2 + 1]);
                    }
                };
            }
            return -1;
        }

        
        if nums[n - 1] <= nums[0] {
            proof {
                let p = (break_pos + 1) as int;
                let k_val = n as int - p;
                assert(Self::is_sorted_range(nums@, 0, p));
                assert(Self::is_sorted_range(nums@, p, n as int));
                assert(nums@[n as int - 1] <= nums@[0]);
                assert(k_val > 0);
                assert(Self::can_sort_by_right_shifts(nums@, k_val));
            }
            return (n - break_pos - 1) as i32;
        }

        proof {
            assert forall |k: int| 0 <= k < n as int implies !Self::can_sort_by_right_shifts(nums@, k) by {
                if k == 0 {
                    assert(nums@[break_pos as int] > nums@[(break_pos + 1) as int]);
                }
            };
        }
        -1
    }
}

}
