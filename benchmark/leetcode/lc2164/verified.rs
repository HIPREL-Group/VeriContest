use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    #[verifier::opaque]
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

    proof fn lemma_swap_preserves_reorder(r: Seq<int>, p: Seq<i32>, s: Seq<i32>, a: int, b: int)
        requires
            Self::is_reorder_of(r, p, s),
            0 <= a < b < r.len(),
        ensures
            Self::is_reorder_of(r.update(a, r[b]).update(b, r[a]), p.update(a, p[b]).update(b, p[a]), s),
    {
        reveal(Solution::is_reorder_of);
        let r2 = r.update(a, r[b]).update(b, r[a]);
        let p2 = p.update(a, p[b]).update(b, p[a]);

        assert forall |x: int, y: int| 0 <= x < r.len() && 0 <= y < r.len() && x != y implies r[x] != r[y] by {
            if x < y {
                assert(r[x] != r[y]);
            } else {
                assert(r[y] != r[x]);
            }
        }

        assert forall |i: int| 0 <= i < r2.len() implies 0 <= #[trigger] r2[i] < r2.len() by {
            if i == a {
                assert(r2[i] == r[b]);
            } else if i == b {
                assert(r2[i] == r[a]);
            } else {
                assert(r2[i] == r[i]);
            }
        }

        assert forall |i: int, j: int| #![trigger r2[i], r2[j]] 0 <= i < j < r2.len() implies r2[i] != r2[j] by {
            let pi: int = if i == a { b } else if i == b { a } else { i };
            let pj: int = if j == a { b } else if j == b { a } else { j };
            assert(r2[i] == r[pi]);
            assert(r2[j] == r[pj]);
            assert(pi != pj);
            assert(r[pi] != r[pj]);
        }

        assert forall |i: int| 0 <= i < r2.len() implies #[trigger] p2[i] == s[r2[i]] by {
            if i == a {
                assert(p2[i] == p[b]);
                assert(p[b] == s[r[b]]);
                assert(r2[i] == r[b]);
            } else if i == b {
                assert(p2[i] == p[a]);
                assert(p[a] == s[r[a]]);
                assert(r2[i] == r[a]);
            } else {
                assert(p2[i] == p[i]);
                assert(p[i] == s[r[i]]);
                assert(r2[i] == r[i]);
            }
        }
        assert(p2 =~= r2.map_values(|i: int| s[i]));
    }

    pub fn sort_even_odd(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result.len() == nums.len(),
            Self::even_indices_sorted(result@),
            Self::odd_indices_sorted(result@),
            exists |r: Seq<int>| Self::is_reorder_of(r, result@, nums@)
                && forall |i: int| 0 <= i < r.len() ==> #[trigger] r[i] % 2 == i % 2,
    {
        let mut nums = nums;
        let ghost old_nums = nums@;
        let ghost mut r: Seq<int> = Seq::new(nums@.len(), |i: int| i);
        proof {
            reveal(Solution::is_reorder_of);
            assert(Self::is_reorder_of(r, nums@, old_nums));
            assert(forall |i: int| 0 <= i < r.len() ==> #[trigger] r[i] % 2 == i % 2);
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
                r.len() == n as int,
                Self::is_reorder_of(r, nums@, old_nums),
                forall |k: int| 0 <= k < r.len() ==> #[trigger] r[k] % 2 == k % 2,
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
                    r.len() == n as int,
                    Self::is_reorder_of(r, nums@, old_nums),
                    forall |k: int| 0 <= k < r.len() ==> #[trigger] r[k] % 2 == k % 2,
                decreases j,
            {
                proof {
                    Self::lemma_swap_preserves_reorder(r, nums@, old_nums, j as int - 2, j as int);
                    let r2 = r.update(j as int - 2, r[j as int]).update(j as int, r[j as int - 2]);
                    assert forall |k: int| 0 <= k < r2.len() implies #[trigger] r2[k] % 2 == k % 2 by {
                        if k == j as int - 2 {
                            assert(r2[k] == r[j as int]);
                        } else if k == j as int {
                            assert(r2[k] == r[j as int - 2]);
                        } else {
                            assert(r2[k] == r[k]);
                        }
                    }
                    r = r2;
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
                r.len() == n as int,
                Self::is_reorder_of(r, nums@, old_nums),
                forall |k: int| 0 <= k < r.len() ==> #[trigger] r[k] % 2 == k % 2,
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
                    r.len() == n as int,
                    Self::is_reorder_of(r, nums@, old_nums),
                    forall |k: int| 0 <= k < r.len() ==> #[trigger] r[k] % 2 == k % 2,
                decreases j,
            {
                proof {
                    Self::lemma_swap_preserves_reorder(r, nums@, old_nums, j as int - 2, j as int);
                    let r2 = r.update(j as int - 2, r[j as int]).update(j as int, r[j as int - 2]);
                    assert forall |k: int| 0 <= k < r2.len() implies #[trigger] r2[k] % 2 == k % 2 by {
                        if k == j as int - 2 {
                            assert(r2[k] == r[j as int]);
                        } else if k == j as int {
                            assert(r2[k] == r[j as int - 2]);
                        } else {
                            assert(r2[k] == r[k]);
                        }
                    }
                    r = r2;
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
            assert(exists |rw: Seq<int>| Self::is_reorder_of(rw, nums@, old_nums)
                && forall |k: int| 0 <= k < rw.len() ==> #[trigger] rw[k] % 2 == k % 2) by {
                assert(Self::is_reorder_of(r, nums@, old_nums));
            }
        }
        nums
    }
}

}
