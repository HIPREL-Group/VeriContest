use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sorted_between(a: Seq<i32>, from: int, to: int) -> bool {
        forall |i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
    }

    pub open spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
        &&& r.len() == s.len()
        &&& p.len() == s.len()
        &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
        &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
        &&& p =~= r.map_values(|i: int| s[i])
    }

    pub open spec fn op_cost_at(v: int, idx: int, mid: int, k: int) -> int {
        if idx < mid {
            if v > k { v - k } else { 0 }
        } else if idx == mid {
            if v >= k { v - k } else { k - v }
        } else {
            if v < k { k - v } else { 0 }
        }
    }

    pub open spec fn cost_prefix(s: Seq<i32>, k: int, mid: int, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else if n > s.len() {
            Self::cost_prefix(s, k, mid, s.len() as int)
        } else {
            Self::cost_prefix(s, k, mid, n - 1)
                + Self::op_cost_at(s[n - 1] as int, n - 1, mid, k)
        }
    }

    pub open spec fn cost_all(s: Seq<i32>, k: int) -> int {
        Self::cost_prefix(s, k, (s.len() / 2) as int, s.len() as int)
    }

    pub fn min_operations_to_make_median_k(nums: Vec<i32>, k: i32) -> (result: i64)
        requires
            1 <= nums.len() <= 200000,
            1 <= k <= 1000000000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
        ensures
            exists|s: Seq<i32>, r: Seq<int>|
                Self::sorted_between(s, 0, s.len() as int)
                && Self::is_reorder_of(r, s, nums@)
                && result as int == Self::cost_all(s, k as int),
    {
        let mut a = nums;
        let ghost old_nums = a@;
        proof {
            let r = Seq::new(a@.len(), |i: int| i);
            assert(Self::is_reorder_of(r, a@, old_nums));
        }
        let n = a.len();

        if n > 0 {
            let mut i: usize = 1;
            while i < n
                invariant
                    n == a.len(),
                    old_nums.len() == n as int,
                    1 <= n <= 200000,
                    1 <= i <= n,
                    1 <= k <= 1000000000,
                    forall |t: int| 0 <= t < n as int ==> 1 <= #[trigger] a[t] <= 1000000000,
                    Self::sorted_between(a@, 0, i as int),
                    exists|r: Seq<int>| Self::is_reorder_of(r, a@, old_nums),
                decreases n - i,
            {
                let mut j = i;
                while j != 0
                    invariant
                        n == a.len(),
                        old_nums.len() == n as int,
                        1 <= n <= 200000,
                        0 <= j <= i < n,
                        1 <= k <= 1000000000,
                        forall |t: int| 0 <= t < n as int ==> 1 <= #[trigger] a[t] <= 1000000000,
                        forall|x: int, y: int| 0 <= x <= y <= i as int ==> x != j as int && y != j as int ==> a[x] <= a[y],
                        Self::sorted_between(a@, j as int, i as int + 1),
                        exists|r: Seq<int>| Self::is_reorder_of(r, a@, old_nums),
                    decreases j,
                {
                    if a[j - 1] > a[j] {
                        proof {
                            let r1 = choose|r: Seq<int>| Self::is_reorder_of(r, a@, old_nums);
                            let r2 = r1.update(j - 1, r1[j as int]).update(j as int, r1[j - 1]);
                            assert(Self::is_reorder_of(
                                r2,
                                a@.update(j - 1, a@[j as int]).update(j as int, a@[j - 1]),
                                old_nums,
                            ));
                        }
                        let left = a[j - 1];
                        let right = a[j];
                        a.set(j - 1, right);
                        a.set(j, left);
                    }
                    j = j - 1;
                }
                i = i + 1;
            }
        }

        let mid = n / 2;
        let mut ans: i128 = 0;
        let mut idx: usize = 0;
        while idx < n
            invariant
                n == a.len(),
                old_nums.len() == n as int,
                1 <= n <= 200000,
                1 <= k <= 1000000000,
                mid == n / 2,
                0 <= idx <= n,
                forall |t: int| 0 <= t < n as int ==> 1 <= #[trigger] a[t] <= 1000000000,
                Self::sorted_between(a@, 0, n as int),
                exists|r: Seq<int>| Self::is_reorder_of(r, a@, old_nums),
                ans as int == Self::cost_prefix(a@, k as int, mid as int, idx as int),
                0 <= ans as int <= idx as int * 1000000000,
            decreases n - idx,
        {
            let ghost old_ans = ans as int;
            let v = a[idx];

            if idx < mid {
                if v > k {
                    let d = v - k;
                    ans = ans + d as i128;
                }
                proof {
                    if v > k {
                        assert(Self::op_cost_at(v as int, idx as int, mid as int, k as int) == v as int - k as int);
                    } else {
                        assert(Self::op_cost_at(v as int, idx as int, mid as int, k as int) == 0);
                    }
                }
            } else if idx == mid {
                if v >= k {
                    let d = v - k;
                    ans = ans + d as i128;
                } else {
                    let d = k - v;
                    ans = ans + d as i128;
                }
                proof {
                    if v >= k {
                        assert(Self::op_cost_at(v as int, idx as int, mid as int, k as int) == v as int - k as int);
                    } else {
                        assert(Self::op_cost_at(v as int, idx as int, mid as int, k as int) == k as int - v as int);
                    }
                }
            } else {
                if v < k {
                    let d = k - v;
                    ans = ans + d as i128;
                }
                proof {
                    if v < k {
                        assert(Self::op_cost_at(v as int, idx as int, mid as int, k as int) == k as int - v as int);
                    } else {
                        assert(Self::op_cost_at(v as int, idx as int, mid as int, k as int) == 0);
                    }
                }
            }

            proof {
                assert(1 <= v <= 1000000000);
                if idx < mid {
                    if v > k {
                        assert(0 < v as int - k as int <= 1000000000);
                    }
                } else if idx == mid {
                    if v >= k {
                        assert(0 <= v as int - k as int <= 1000000000);
                    } else {
                        assert(0 < k as int - v as int <= 1000000000);
                    }
                } else {
                    if v < k {
                        assert(0 < k as int - v as int <= 1000000000);
                    }
                }

                assert(Self::cost_prefix(a@, k as int, mid as int, idx as int + 1)
                    == Self::cost_prefix(a@, k as int, mid as int, idx as int)
                    + Self::op_cost_at(a@[idx as int] as int, idx as int, mid as int, k as int));
                assert(a@[idx as int] == v);
                assert(ans as int == old_ans + Self::op_cost_at(v as int, idx as int, mid as int, k as int));
                assert(ans as int == Self::cost_prefix(a@, k as int, mid as int, idx as int + 1));

                assert(0 <= Self::op_cost_at(v as int, idx as int, mid as int, k as int) <= 1000000000) by {
                    if idx < mid {
                        if v > k {
                            assert(Self::op_cost_at(v as int, idx as int, mid as int, k as int) == v as int - k as int);
                        } else {
                            assert(Self::op_cost_at(v as int, idx as int, mid as int, k as int) == 0);
                        }
                    } else if idx == mid {
                        if v >= k {
                            assert(Self::op_cost_at(v as int, idx as int, mid as int, k as int) == v as int - k as int);
                        } else {
                            assert(Self::op_cost_at(v as int, idx as int, mid as int, k as int) == k as int - v as int);
                        }
                    } else {
                        if v < k {
                            assert(Self::op_cost_at(v as int, idx as int, mid as int, k as int) == k as int - v as int);
                        } else {
                            assert(Self::op_cost_at(v as int, idx as int, mid as int, k as int) == 0);
                        }
                    }
                };

                assert(0 <= ans as int);
                assert(ans as int <= (idx as int + 1) * 1000000000);
            }

            idx = idx + 1;
        }

        proof {
            assert(idx == n);
            assert(ans as int == Self::cost_prefix(a@, k as int, mid as int, n as int));
            assert(mid as int == (a@.len() / 2) as int);
            assert(ans as int == Self::cost_all(a@, k as int));
            assert(old_nums == nums@);

            let r_final = choose|r: Seq<int>| Self::is_reorder_of(r, a@, old_nums);
            assert(exists|s: Seq<i32>, r: Seq<int>|
                Self::sorted_between(s, 0, s.len() as int)
                && Self::is_reorder_of(r, s, nums@)
                && (ans as i64) as int == Self::cost_all(s, k as int)) by {
                let s = a@;
                let r = r_final;
                assert(Self::sorted_between(s, 0, s.len() as int));
                assert(Self::is_reorder_of(r, s, nums@));
                assert((ans as i64) as int == ans as int);
                assert(ans as int == Self::cost_all(s, k as int));
            };
        }

        ans as i64
    }
}

}
