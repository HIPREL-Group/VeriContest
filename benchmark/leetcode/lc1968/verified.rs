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

    pub open spec fn not_average_at(s: Seq<i32>, i: int) -> bool {
        &&& 1 <= i < s.len() - 1
        &&& 2 * (s[i] as int) != (s[i - 1] as int) + (s[i + 1] as int)
    }

    pub open spec fn good_adjacent(s: Seq<i32>, i: int) -> bool {
        &&& 1 <= i < s.len()
        &&& if i % 2 == 1 { s[i - 1] < s[i] } else { s[i - 1] > s[i] }
    }

    proof fn distinct_indices_imply_distinct_values(s: Seq<i32>, i: int, j: int)
        requires
            forall |a: int, b: int| 0 <= a < b < s.len() ==> s[a] != s[b],
            0 <= i < s.len(),
            0 <= j < s.len(),
            i != j,
        ensures
            s[i] != s[j],
    {
        if i < j {
            assert(s[i] != s[j]);
        } else {
            assert(j < i);
            assert(s[j] != s[i]);
        }
    }

    proof fn good_adjacent_implies_not_average(s: Seq<i32>, i: int)
        requires
            Self::good_adjacent(s, i),
            Self::good_adjacent(s, i + 1),
        ensures
            Self::not_average_at(s, i),
    {
        if i % 2 == 1 {
            assert(s[i - 1] < s[i]);
            assert(s[i + 1] < s[i]);
            assert((s[i - 1] as int) + (s[i + 1] as int) < 2 * (s[i] as int));
        } else {
            assert(s[i - 1] > s[i]);
            assert(s[i + 1] > s[i]);
            assert((s[i - 1] as int) + (s[i + 1] as int) > 2 * (s[i] as int));
        }
    }

    pub fn rearrange_array(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            3 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
        ensures
            result.len() == nums.len(),
            exists |r: Seq<int>| Self::is_reorder_of(r, result@, nums@),
            forall |i: int| 1 <= i < result.len() - 1 ==> #[trigger] Self::not_average_at(result@, i),
    {
        let mut nums = nums;
        let ghost old_nums = nums@;
        proof {
            let r = Seq::new(nums@.len(), |i: int| i);
            assert(Self::is_reorder_of(r, nums@, old_nums));
        }
        let n = nums.len();
        let mut i: usize = 1;
        while i < n
            invariant
                n == nums.len(),
                old_nums.len() == n as int,
                3 <= n <= 100_000,
                1 <= i <= n,
                forall |a: int, b: int| 0 <= a < b < old_nums.len() ==> old_nums[a] != old_nums[b],
                exists |r: Seq<int>| Self::is_reorder_of(r, nums@, old_nums),
                forall |k: int| 1 <= k < i as int ==> #[trigger] Self::good_adjacent(nums@, k),
            decreases n - i,
        {
            if i % 2 == 1 {
                if nums[i - 1] >= nums[i] {
                    let ghost before = nums@;
                    let left = nums[i - 1];
                    let right = nums[i];
                    nums.set(i - 1, right);
                    nums.set(i, left);
                    proof {
                        let i_int = i as int;
                        let r1 = choose |r: Seq<int>| Self::is_reorder_of(r, before, old_nums);
                        assert(before[i_int - 1] == old_nums[r1[i_int - 1]]);
                        assert(before[i_int] == old_nums[r1[i_int]]);
                        assert(r1[i_int - 1] != r1[i_int]);
                        Self::distinct_indices_imply_distinct_values(old_nums, r1[i_int - 1], r1[i_int]);
                        assert(left == before[i_int - 1]);
                        assert(right == before[i_int]);
                        assert(left != right);
                        assert(left > right);
                        let r2 = r1.update(i_int - 1, r1[i_int]).update(i_int, r1[i_int - 1]);
                        assert(Self::is_reorder_of(r2, before.update(i_int - 1, before[i_int]).update(i_int, before[i_int - 1]), old_nums));
                        assert(nums@ =~= before.update(i_int - 1, before[i_int]).update(i_int, before[i_int - 1]));
                        assert(Self::is_reorder_of(r2, nums@, old_nums));
                        assert(Self::good_adjacent(nums@, i_int));
                        if i >= 2 {
                            assert(Self::good_adjacent(before, i_int - 1));
                            assert(before[i_int - 2] > before[i_int - 1]);
                            assert(before[i_int - 1] > before[i_int]);
                            assert(nums@[i_int - 2] == before[i_int - 2]);
                            assert(nums@[i_int - 1] == before[i_int]);
                            assert(Self::good_adjacent(nums@, i_int - 1));
                        }
                        assert forall |k: int| 1 <= k < i_int + 1 implies #[trigger] Self::good_adjacent(nums@, k) by {
                            if k < i_int - 1 {
                                assert(Self::good_adjacent(before, k));
                                assert(nums@[k - 1] == before[k - 1]);
                                assert(nums@[k] == before[k]);
                            } else if k == i_int - 1 {
                                assert(i >= 2);
                            } else {
                                assert(k == i_int);
                            }
                        }
                    }
                } else {
                    proof {
                        assert(Self::good_adjacent(nums@, i as int));
                        assert forall |k: int| 1 <= k < i as int + 1 implies #[trigger] Self::good_adjacent(nums@, k) by {
                            if k < i as int {
                                assert(Self::good_adjacent(nums@, k));
                            } else {
                                assert(k == i as int);
                            }
                        }
                    }
                }
            } else {
                if nums[i - 1] <= nums[i] {
                    let ghost before = nums@;
                    let left = nums[i - 1];
                    let right = nums[i];
                    nums.set(i - 1, right);
                    nums.set(i, left);
                    proof {
                        let i_int = i as int;
                        let r1 = choose |r: Seq<int>| Self::is_reorder_of(r, before, old_nums);
                        assert(before[i_int - 1] == old_nums[r1[i_int - 1]]);
                        assert(before[i_int] == old_nums[r1[i_int]]);
                        assert(r1[i_int - 1] != r1[i_int]);
                        Self::distinct_indices_imply_distinct_values(old_nums, r1[i_int - 1], r1[i_int]);
                        assert(left == before[i_int - 1]);
                        assert(right == before[i_int]);
                        assert(left != right);
                        assert(left < right);
                        let r2 = r1.update(i_int - 1, r1[i_int]).update(i_int, r1[i_int - 1]);
                        assert(Self::is_reorder_of(r2, before.update(i_int - 1, before[i_int]).update(i_int, before[i_int - 1]), old_nums));
                        assert(nums@ =~= before.update(i_int - 1, before[i_int]).update(i_int, before[i_int - 1]));
                        assert(Self::is_reorder_of(r2, nums@, old_nums));
                        assert(Self::good_adjacent(nums@, i_int));
                        if i >= 2 {
                            assert(Self::good_adjacent(before, i_int - 1));
                            assert(before[i_int - 2] < before[i_int - 1]);
                            assert(before[i_int - 1] < before[i_int]);
                            assert(nums@[i_int - 2] == before[i_int - 2]);
                            assert(nums@[i_int - 1] == before[i_int]);
                            assert(Self::good_adjacent(nums@, i_int - 1));
                        }
                        assert forall |k: int| 1 <= k < i_int + 1 implies #[trigger] Self::good_adjacent(nums@, k) by {
                            if k < i_int - 1 {
                                assert(Self::good_adjacent(before, k));
                                assert(nums@[k - 1] == before[k - 1]);
                                assert(nums@[k] == before[k]);
                            } else if k == i_int - 1 {
                                assert(i >= 2);
                            } else {
                                assert(k == i_int);
                            }
                        }
                    }
                } else {
                    proof {
                        assert(Self::good_adjacent(nums@, i as int));
                        assert forall |k: int| 1 <= k < i as int + 1 implies #[trigger] Self::good_adjacent(nums@, k) by {
                            if k < i as int {
                                assert(Self::good_adjacent(nums@, k));
                            } else {
                                assert(k == i as int);
                            }
                        }
                    }
                }
            }
            i = i + 1;
        }
        proof {
            assert forall |k: int| 1 <= k < nums.len() as int - 1 implies #[trigger] Self::not_average_at(nums@, k) by {
                assert(Self::good_adjacent(nums@, k));
                assert(Self::good_adjacent(nums@, k + 1));
                Self::good_adjacent_implies_not_average(nums@, k);
            }
        }
        nums
    }
}

}
