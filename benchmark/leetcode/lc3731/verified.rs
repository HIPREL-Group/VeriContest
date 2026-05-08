use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_contains(nums: Seq<i32>, x: i32) -> bool {
        exists |i: int| 0 <= i < nums.len() && nums[i] == x
    }

    pub open spec fn strictly_increasing(nums: Seq<i32>) -> bool {
        forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j]
    }

    pub open spec fn is_lower_bound(nums: Seq<i32>, lo: i32) -> bool {
        Self::seq_contains(nums, lo)
            && forall |i: int| 0 <= i < nums.len() ==> lo <= nums[i]
    }

    pub open spec fn is_upper_bound(nums: Seq<i32>, hi: i32) -> bool {
        Self::seq_contains(nums, hi)
            && forall |i: int| 0 <= i < nums.len() ==> nums[i] <= hi
    }

    pub fn find_missing_elements(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
        ensures
            exists |lo: i32, hi: i32|
                Self::is_lower_bound(nums@, lo)
                && Self::is_upper_bound(nums@, hi)
                && forall |i: int|
                    0 <= i < result.len() ==> lo < #[trigger] result@[i] < hi && !Self::seq_contains(nums@, result@[i])
                && forall |x: i32|
                    lo < x < hi && !Self::seq_contains(nums@, x) ==> #[trigger] Self::seq_contains(result@, x)
                && Self::strictly_increasing(result@),
    {
        let n = nums.len();
        let mut min_v = nums[0];
        let mut max_v = nums[0];
        let mut i: usize = 1;

        while i < n
            invariant
                n == nums.len(),
                2 <= n <= 100,
                1 <= i <= n,
                forall |idx: int| 0 <= idx < n ==> 1 <= #[trigger] nums@[idx] <= 100,
                forall |a: int, b: int| 0 <= a < b < n ==> nums@[a] != nums@[b],
                forall |j: int| 0 <= j < i ==> min_v <= #[trigger] nums@[j],
                forall |j: int| 0 <= j < i ==> #[trigger] nums@[j] <= max_v,
                exists |j: int| 0 <= j < i && nums@[j] == min_v,
                exists |j: int| 0 <= j < i && nums@[j] == max_v,
            decreases n - i,
        {
            if nums[i] < min_v {
                min_v = nums[i];
            }
            if nums[i] > max_v {
                max_v = nums[i];
            }
            i = i + 1;
        }

        proof {
            assert(Self::is_lower_bound(nums@, min_v));
            assert(Self::is_upper_bound(nums@, max_v));
            assert(min_v < max_v) by {
                if min_v >= max_v {
                    assert(min_v == max_v);
                    assert(nums@[0] == min_v);
                    assert(nums@[1] == max_v);
                    assert(nums@[0] == nums@[1]);
                    assert(nums@[0] != nums@[1]);
                }
            }
        }

        let mut result: Vec<i32> = Vec::new();
        let mut k = min_v + 1;

        while k < max_v
            invariant
                n == nums.len(),
                2 <= n <= 100,
                min_v < max_v,
                min_v + 1 <= k <= max_v,
                Self::is_lower_bound(nums@, min_v),
                Self::is_upper_bound(nums@, max_v),
                forall |ri: int|
                    0 <= ri < result.len() ==> min_v < #[trigger] result@[ri] < k && !Self::seq_contains(nums@, result@[ri]),
                forall |x: i32|
                    min_v < x < k && !Self::seq_contains(nums@, x) ==> #[trigger] Self::seq_contains(result@, x),
                Self::strictly_increasing(result@),
            decreases (max_v - k) as int,
        {
            let mut found = false;
            let mut j: usize = 0;

            while j < n
                invariant
                    n == nums.len(),
                    0 <= j <= n,
                    found ==> (exists |t: int| 0 <= t < j && nums@[t] == k),
                    !found ==> (forall |t: int| 0 <= t < j ==> nums@[t] != k),
                decreases n - j,
            {
                if nums[j] == k {
                    found = true;
                }
                j = j + 1;
            }

            proof {
                assert(j == n);
                assert(found <==> Self::seq_contains(nums@, k)) by {
                    if found {
                        let t = choose |t: int| 0 <= t < j && nums@[t] == k;
                        assert(0 <= t < n);
                    } else {
                        if Self::seq_contains(nums@, k) {
                            let t = choose |t: int| 0 <= t < n && nums@[t] == k;
                            assert(nums@[t] != k);
                        }
                    }
                }
            }

            if !found {
                let ghost old_result = result@;
                let ghost old_len = result.len();
                result.push(k);

                proof {
                    assert(result@[old_len as int] == k);

                    assert forall |ri: int| 0 <= ri < result.len()
                        implies min_v < #[trigger] result@[ri] < k + 1 && !Self::seq_contains(nums@, result@[ri]) by {
                        if ri < old_len as int {
                            assert(result@[ri] == old_result[ri]);
                        }
                    }

                    assert forall |x: i32|
                        min_v < x < k + 1 && !Self::seq_contains(nums@, x)
                        implies #[trigger] Self::seq_contains(result@, x) by {
                        if x < k {
                            assert(Self::seq_contains(old_result, x));
                            let w = choose |p: int| 0 <= p < old_result.len() && old_result[p] == x;
                            assert(result@[w] == x);
                        } else {
                            assert(x == k);
                            assert(result@[old_len as int] == x);
                        }
                    }

                    assert forall |a: int, b: int| 0 <= a < b < result.len()
                        implies #[trigger] result@[a] < #[trigger] result@[b] by {
                        if b < old_len as int {
                        } else {
                            assert(b == old_len as int);
                            assert(result@[b] == k);
                            assert(result@[a] < k);
                        }
                    }
                }
            } else {
                proof {
                    assert forall |ri: int| 0 <= ri < result.len()
                        implies min_v < #[trigger] result@[ri] < k + 1 && !Self::seq_contains(nums@, result@[ri]) by {
                    }

                    assert forall |x: i32|
                        min_v < x < k + 1 && !Self::seq_contains(nums@, x)
                        implies #[trigger] Self::seq_contains(result@, x) by {
                        if x < k {
                        } else {
                            assert(x == k);
                            assert(Self::seq_contains(nums@, x));
                        }
                    }
                }
            }

            k = k + 1;
        }

        proof {
            assert(k == max_v);
            assert forall |ri: int| 0 <= ri < result.len()
                implies min_v < #[trigger] result@[ri] < max_v && !Self::seq_contains(nums@, result@[ri]) by {
                assert(result@[ri] < k);
            }
            assert forall |x: i32|
                min_v < x < max_v && !Self::seq_contains(nums@, x)
                implies #[trigger] Self::seq_contains(result@, x) by {
            }
        }

        result
    }
}

} 
