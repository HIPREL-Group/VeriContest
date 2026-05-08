use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
        &&& r.len() == s.len()
        &&& p.len() == s.len()
        &&& forall |i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
        &&& forall |i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
        &&& p =~= r.map_values(|i: int| s[i])
    }

    pub open spec fn even_indices_sorted_between(s: Seq<i32>, from: int, to: int) -> bool {
        forall |i: int, j: int| 0 <= i < j < s.len() && from <= i && j < to && i % 2 == 0 && j % 2 == 0 ==> s[i] <= s[j]
    }

    pub open spec fn odd_indices_sorted_between(s: Seq<i32>, from: int, to: int) -> bool {
        forall |i: int, j: int| 0 <= i < j < s.len() && from <= i && j < to && i % 2 == 1 && j % 2 == 1 ==> s[i] >= s[j]
    }

    pub open spec fn even_indices_sorted(s: Seq<i32>) -> bool {
        Self::even_indices_sorted_between(s, 0, s.len() as int)
    }

    pub open spec fn odd_indices_sorted(s: Seq<i32>) -> bool {
        Self::odd_indices_sorted_between(s, 0, s.len() as int)
    }

    pub fn sort_even_odd(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result.len() == nums.len(),
            Self::even_indices_sorted(result@),
            Self::odd_indices_sorted(result@),
            exists |r: Seq<int>| Self::is_reorder_of(r, result@, nums@),
    {
        let mut nums = nums;
        let ghost old_nums = nums@;
        proof {
            let r = Seq::new(nums@.len(), |i: int| i);
            assert(Self::is_reorder_of(r, nums@, old_nums));
        }
        let n = nums.len();
        let mut i: usize = 2;
        while i < n
            invariant
                n == nums.len(),
                old_nums.len() == n as int,
                1 <= n <= 100,
                1 <= i <= n + 2,
                i % 2 == 0,
                forall |k: int| 0 <= k < n as int ==> 1 <= #[trigger] nums[k] <= 100,
                Self::even_indices_sorted_between(nums@, 0, i as int),
                forall |k: int| 0 <= k < n as int && k % 2 == 1 ==> nums[k] == old_nums[k],
                exists |r: Seq<int>| Self::is_reorder_of(r, nums@, old_nums),
            decreases if i < n { (((n - i) as int) + 1) / 2 } else { 0int },
        {
            let mut j: usize = i;
            while j != 0 && nums[j - 2] > nums[j]
                invariant
                    n == nums.len(),
                    old_nums.len() == n as int,
                    1 <= n <= 100,
                    0 <= j <= i < n,
                    i % 2 == 0,
                    j % 2 == 0,
                    forall |k: int| 0 <= k < n as int ==> 1 <= #[trigger] nums[k] <= 100,
                    forall |x: int, y: int| 0 <= x <= y <= i as int && x % 2 == 0 && y % 2 == 0 ==> x != j as int && y != j as int ==> nums[x] <= nums[y],
                    Self::even_indices_sorted_between(nums@, j as int, i as int + 2),
                    forall |k: int| 0 <= k < n as int && k % 2 == 1 ==> nums[k] == old_nums[k],
                    exists |r: Seq<int>| Self::is_reorder_of(r, nums@, old_nums),
                decreases j,
            {
                proof {
                    let r1 = choose |r: Seq<int>| Self::is_reorder_of(r, nums@, old_nums);
                    let r2 = r1.update(j as int - 2, r1[j as int]).update(j as int, r1[j as int - 2]);
                    assert(Self::is_reorder_of(r2, nums@.update(j as int - 2, nums@[j as int]).update(j as int, nums@[j as int - 2]), old_nums));
                }
                let tmp_left = nums[j - 2];
                let tmp_right = nums[j];
                nums[j - 2] = tmp_right;
                nums[j] = tmp_left;
                j = j - 2;
            }
            proof {
                assert forall |x: int, y: int| 0 <= x < y < i as int + 2 && x % 2 == 0 && y % 2 == 0 implies nums[x] <= nums[y] by {
                    if j == 0 {
                        assert(Self::even_indices_sorted_between(nums@, 0, i as int + 2));
                    } else {
                        if x != j as int && y != j as int {
                            assert(x <= y <= i as int);
                        } else if x >= j as int {
                            assert(Self::even_indices_sorted_between(nums@, j as int, i as int + 2));
                        } else {
                            assert(x < j as int);
                            assert(j >= 2);
                            assert(nums[x] <= nums[j as int - 2]);
                            assert(nums[j as int - 2] <= nums[j as int]);
                            if y > j as int {
                                assert(Self::even_indices_sorted_between(nums@, j as int, i as int + 2));
                                assert(nums[j as int] <= nums[y]);
                            }
                        }
                    }
                }
            }
            i = i + 2;
        }
        let ghost even_sorted_nums = nums@;
        let mut i: usize = 3;
        while i < n
            invariant
                n == nums.len(),
                old_nums.len() == n as int,
                1 <= n <= 100,
                1 <= i <= n + 2,
                i % 2 == 1,
                forall |k: int| 0 <= k < n as int ==> 1 <= #[trigger] nums[k] <= 100,
                Self::even_indices_sorted(even_sorted_nums),
                even_sorted_nums.len() == n as int,
                forall |k: int| 0 <= k < n as int && k % 2 == 0 ==> nums[k] == #[trigger] even_sorted_nums[k],
                Self::odd_indices_sorted_between(nums@, 1, i as int),
                exists |r: Seq<int>| Self::is_reorder_of(r, nums@, old_nums),
            decreases if i < n { (((n - i) as int) + 1) / 2 } else { 0int },
        {
            let mut j: usize = i;
            while j > 1 && nums[j - 2] < nums[j]
                invariant
                    n == nums.len(),
                    old_nums.len() == n as int,
                    1 <= n <= 100,
                    1 <= j <= i < n,
                    i % 2 == 1,
                    j % 2 == 1,
                    forall |k: int| 0 <= k < n as int ==> 1 <= #[trigger] nums[k] <= 100,
                    Self::even_indices_sorted(even_sorted_nums),
                    even_sorted_nums.len() == n as int,
                    forall |k: int| 0 <= k < n as int && k % 2 == 0 ==> nums[k] == #[trigger] even_sorted_nums[k],
                    forall |x: int, y: int| 1 <= x <= y <= i as int && x % 2 == 1 && y % 2 == 1 ==> x != j as int && y != j as int ==> nums[x] >= nums[y],
                    Self::odd_indices_sorted_between(nums@, j as int, i as int + 2),
                    exists |r: Seq<int>| Self::is_reorder_of(r, nums@, old_nums),
                decreases j,
            {
                proof {
                    let r1 = choose |r: Seq<int>| Self::is_reorder_of(r, nums@, old_nums);
                    let r2 = r1.update(j as int - 2, r1[j as int]).update(j as int, r1[j as int - 2]);
                    assert(Self::is_reorder_of(r2, nums@.update(j as int - 2, nums@[j as int]).update(j as int, nums@[j as int - 2]), old_nums));
                }
                let tmp_left = nums[j - 2];
                let tmp_right = nums[j];
                nums[j - 2] = tmp_right;
                nums[j] = tmp_left;
                j = j - 2;
            }
            proof {
                assert forall |x: int, y: int| 0 <= x < y < nums.len() && x % 2 == 0 && y % 2 == 0 implies nums[x] <= nums[y] by {
                    assert(nums[x] == even_sorted_nums[x]);
                    assert(nums[y] == even_sorted_nums[y]);
                    assert(Self::even_indices_sorted(even_sorted_nums));
                }
                assert forall |x: int, y: int| 1 <= x < y < i as int + 2 && x % 2 == 1 && y % 2 == 1 implies nums[x] >= nums[y] by {
                    if j == 1 {
                        assert(Self::odd_indices_sorted_between(nums@, 1, i as int + 2));
                    } else {
                        if x != j as int && y != j as int {
                            assert(x <= y <= i as int);
                        } else if x >= j as int {
                            assert(Self::odd_indices_sorted_between(nums@, j as int, i as int + 2));
                        } else {
                            assert(x < j as int);
                            assert(j >= 3);
                            assert(nums[x] >= nums[j as int - 2]);
                            assert(nums[j as int - 2] >= nums[j as int]);
                            if y > j as int {
                                assert(Self::odd_indices_sorted_between(nums@, j as int, i as int + 2));
                                assert(nums[j as int] >= nums[y]);
                            }
                        }
                    }
                }
            }
            i = i + 2;
        }
        proof {
            assert forall |x: int, y: int| 0 <= x < y < nums.len() && x % 2 == 0 && y % 2 == 0 implies nums[x] <= nums[y] by {
                assert(nums[x] == even_sorted_nums[x]);
                assert(nums[y] == even_sorted_nums[y]);
                assert(Self::even_indices_sorted(even_sorted_nums));
            }
            assert forall |x: int, y: int| 0 <= x < y < nums.len() && x % 2 == 1 && y % 2 == 1 implies nums[x] >= nums[y] by {
                assert(1 <= x);
                assert(y < i as int);
                assert(Self::odd_indices_sorted_between(nums@, 1, i as int));
            }
        }
        nums
    }
}

}