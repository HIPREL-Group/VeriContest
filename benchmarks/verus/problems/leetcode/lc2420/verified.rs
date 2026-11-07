use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn good_index(nums: Seq<i32>, k: int, idx: int) -> bool {
        0 <= idx < nums.len()
        && 1 <= k
        && k <= idx
        && idx + k < nums.len()
        && (forall |j: int| idx - k <= j < idx - 1 ==> #[trigger] nums[j] >= nums[j + 1])
        && (forall |j: int| idx + 1 <= j < idx + k ==> #[trigger] nums[j] <= nums[j + 1])
    }

    pub open spec fn inc_bad_step(nums: Seq<i32>, i: int) -> int
        recommends
            0 <= i + 1 < nums.len(),
    {
        if nums[i] < nums[i + 1] { 1 } else { 0 }
    }

    pub open spec fn dec_bad_step(nums: Seq<i32>, i: int) -> int
        recommends
            0 <= i + 1 < nums.len(),
    {
        if nums[i] > nums[i + 1] { 1 } else { 0 }
    }

    pub open spec fn inc_bad_prefix(nums: Seq<i32>, end: int) -> int
        recommends
            0 <= end < nums.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::inc_bad_prefix(nums, end - 1) + Self::inc_bad_step(nums, end - 1)
        }
    }

    pub open spec fn dec_bad_prefix(nums: Seq<i32>, end: int) -> int
        recommends
            0 <= end < nums.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::dec_bad_prefix(nums, end - 1) + Self::dec_bad_step(nums, end - 1)
        }
    }

    proof fn lemma_inc_bad_prefix_monotonic(nums: Seq<i32>, left: int, right: int)
        requires
            0 <= left <= right < nums.len(),
        ensures
            Self::inc_bad_prefix(nums, left) <= Self::inc_bad_prefix(nums, right),
        decreases right - left,
    {
        if left < right {
            Self::lemma_inc_bad_prefix_monotonic(nums, left, right - 1);
            assert(Self::inc_bad_prefix(nums, right) == Self::inc_bad_prefix(nums, right - 1) + Self::inc_bad_step(nums, right - 1));
            assert(0 <= Self::inc_bad_step(nums, right - 1));
        }
    }

    proof fn lemma_dec_bad_prefix_monotonic(nums: Seq<i32>, left: int, right: int)
        requires
            0 <= left <= right < nums.len(),
        ensures
            Self::dec_bad_prefix(nums, left) <= Self::dec_bad_prefix(nums, right),
        decreases right - left,
    {
        if left < right {
            Self::lemma_dec_bad_prefix_monotonic(nums, left, right - 1);
            assert(Self::dec_bad_prefix(nums, right) == Self::dec_bad_prefix(nums, right - 1) + Self::dec_bad_step(nums, right - 1));
            assert(0 <= Self::dec_bad_step(nums, right - 1));
        }
    }

    proof fn lemma_inc_bad_prefix_difference_has_bad(nums: Seq<i32>, left: int, right: int)
        requires
            0 <= left <= right < nums.len(),
            Self::inc_bad_prefix(nums, left) < Self::inc_bad_prefix(nums, right),
        ensures
            exists |m: int| left <= m < right && #[trigger] Self::inc_bad_step(nums, m) == 1,
        decreases right - left,
    {
        if left == right {
            assert(false);
        } else if Self::inc_bad_step(nums, right - 1) == 1 {
            assert(left <= right - 1 < right);
        } else {
            assert(Self::inc_bad_prefix(nums, right) == Self::inc_bad_prefix(nums, right - 1));
            Self::lemma_inc_bad_prefix_difference_has_bad(nums, left, right - 1);
        }
    }

    proof fn lemma_dec_bad_prefix_difference_has_bad(nums: Seq<i32>, left: int, right: int)
        requires
            0 <= left <= right < nums.len(),
            Self::dec_bad_prefix(nums, left) < Self::dec_bad_prefix(nums, right),
        ensures
            exists |m: int| left <= m < right && #[trigger] Self::dec_bad_step(nums, m) == 1,
        decreases right - left,
    {
        if left == right {
            assert(false);
        } else if Self::dec_bad_step(nums, right - 1) == 1 {
            assert(left <= right - 1 < right);
        } else {
            assert(Self::dec_bad_prefix(nums, right) == Self::dec_bad_prefix(nums, right - 1));
            Self::lemma_dec_bad_prefix_difference_has_bad(nums, left, right - 1);
        }
    }

    pub fn good_indices(nums: Vec<i32>, k: i32) -> (result: Vec<i32>)
        requires
            3 <= nums.len() <= 100_000,
            1 <= k as int <= nums.len() as int / 2,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000,
        ensures
            forall |i: int| 0 <= i < result@.len() ==>
                0 <= result@[i] < nums.len() as i32
                && Self::good_index(nums@, k as int, result@[i] as int),
            forall |idx: int| 0 <= idx < nums.len() && Self::good_index(nums@, k as int, idx)
                ==> #[trigger] result@.contains(idx as i32),
            forall |a: int, b: int| 0 <= a < b < result@.len() ==> result@[a] < result@[b],
    {
        let n = nums.len();
        let k_usize = k as usize;

        let mut inc_prefix: Vec<i32> = Vec::new();
        let mut dec_prefix: Vec<i32> = Vec::new();
        inc_prefix.push(0);
        dec_prefix.push(0);

        let mut i: usize = 1;
        while i < n
            invariant
                n == nums.len(),
                3 <= n <= 100_000,
                1 <= k as int <= n as int / 2,
                k_usize as int == k as int,
                1 <= k_usize <= n / 2,
                1 <= i <= n,
                forall |m: int| 0 <= m < n ==> 1 <= #[trigger] nums[m] <= 1_000_000,
                inc_prefix.len() == i,
                dec_prefix.len() == i,
                forall |m: int| 0 <= m < i as int ==> #[trigger] inc_prefix[m] as int == Self::inc_bad_prefix(nums@, m),
                forall |m: int| 0 <= m < i as int ==> #[trigger] dec_prefix[m] as int == Self::dec_bad_prefix(nums@, m),
                forall |m: int| 0 <= m < i as int ==> 0 <= #[trigger] inc_prefix[m] as int <= m,
                forall |m: int| 0 <= m < i as int ==> 0 <= #[trigger] dec_prefix[m] as int <= m,
            decreases n - i,
        {
            let prev = nums[i - 1];
            let curr = nums[i];

            let mut inc_next = inc_prefix[i - 1];
            if prev < curr {
                proof {
                    assert(0 <= inc_prefix[i as int - 1] as int <= i as int - 1);
                    assert(inc_next as int == inc_prefix[i as int - 1] as int);
                    assert(i as int - 1 < 2_147_483_647);
                    assert(inc_next < 2_147_483_647);
                }
                inc_next += 1;
            }

            let mut dec_next = dec_prefix[i - 1];
            if prev > curr {
                dec_next += 1;
            }

            let ghost old_inc = inc_prefix@;
            let ghost old_dec = dec_prefix@;
            inc_prefix.push(inc_next);
            dec_prefix.push(dec_next);
            proof {
                assert(inc_prefix@ == old_inc.push(inc_next));
                assert(dec_prefix@ == old_dec.push(dec_next));
                assert(Self::inc_bad_prefix(nums@, i as int) == Self::inc_bad_prefix(nums@, i as int - 1) + Self::inc_bad_step(nums@, i as int - 1));
                assert(Self::dec_bad_prefix(nums@, i as int) == Self::dec_bad_prefix(nums@, i as int - 1) + Self::dec_bad_step(nums@, i as int - 1));
                assert(inc_prefix[i as int - 1] as int == Self::inc_bad_prefix(nums@, i as int - 1));
                assert(dec_prefix[i as int - 1] as int == Self::dec_bad_prefix(nums@, i as int - 1));
                assert(prev == nums[i as int - 1]);
                assert(curr == nums[i as int]);
                if prev < curr {
                    assert(Self::inc_bad_step(nums@, i as int - 1) == 1);
                    assert(inc_next as int == inc_prefix[i as int - 1] as int + 1);
                    assert(inc_next as int == Self::inc_bad_prefix(nums@, i as int));
                } else {
                    assert(Self::inc_bad_step(nums@, i as int - 1) == 0);
                    assert(inc_next as int == Self::inc_bad_prefix(nums@, i as int));
                }
                if prev > curr {
                    assert(Self::dec_bad_step(nums@, i as int - 1) == 1);
                    assert(dec_next as int == Self::dec_bad_prefix(nums@, i as int));
                } else {
                    assert(Self::dec_bad_step(nums@, i as int - 1) == 0);
                    assert(dec_next as int == Self::dec_bad_prefix(nums@, i as int));
                }
                assert forall |m: int| 0 <= m < i as int + 1 implies #[trigger] inc_prefix[m] as int == Self::inc_bad_prefix(nums@, m) by {
                    if m < i as int {
                        assert(inc_prefix@[m] == old_inc[m]);
                    } else {
                        assert(m == i as int);
                    }
                }
                assert forall |m: int| 0 <= m < i as int + 1 implies #[trigger] dec_prefix[m] as int == Self::dec_bad_prefix(nums@, m) by {
                    if m < i as int {
                        assert(dec_prefix@[m] == old_dec[m]);
                    } else {
                        assert(m == i as int);
                    }
                }
                assert forall |m: int| 0 <= m < i as int + 1 implies 0 <= #[trigger] inc_prefix[m] as int <= m by {
                    if m < i as int {
                    } else {
                        assert(m == i as int);
                        if prev < curr {
                            assert(inc_prefix[m] as int == inc_prefix[m - 1] as int + 1);
                        }
                    }
                }
                assert forall |m: int| 0 <= m < i as int + 1 implies 0 <= #[trigger] dec_prefix[m] as int <= m by {
                    if m < i as int {
                    } else {
                        assert(m == i as int);
                        if prev > curr {
                            assert(dec_prefix[m] as int == dec_prefix[m - 1] as int + 1);
                        }
                    }
                }
            }
            i += 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut idx = k_usize;
        while idx + k_usize < n
            invariant
                n == nums.len(),
                3 <= n <= 100_000,
                1 <= k as int <= n as int / 2,
                k_usize as int == k as int,
                1 <= k_usize <= n / 2,
                forall |m: int| 0 <= m < n ==> 1 <= #[trigger] nums[m] <= 1_000_000,
                inc_prefix.len() == n,
                dec_prefix.len() == n,
                forall |m: int| 0 <= m < n as int ==> #[trigger] inc_prefix[m] as int == Self::inc_bad_prefix(nums@, m),
                forall |m: int| 0 <= m < n as int ==> #[trigger] dec_prefix[m] as int == Self::dec_bad_prefix(nums@, m),
                k_usize <= idx <= n - k_usize,
                forall |m: int| 0 <= m < result@.len() ==>
                    0 <= result@[m] < idx as i32
                    && Self::good_index(nums@, k as int, result@[m] as int),
                forall |cand: int|
                    k as int <= cand < idx as int
                    && cand + (k as int) < (n as int)
                    && inc_prefix[cand - 1] == inc_prefix[cand - (k as int)]
                    && dec_prefix[cand + (k as int)] == dec_prefix[cand + 1]
                    ==> #[trigger] result@.contains(cand as i32),
                forall |a: int, b: int| 0 <= a < b < result@.len() ==> result@[a] < result@[b],
            decreases n - k_usize - idx,
        {
            let idx_i = idx as i32;
            if inc_prefix[idx - 1] == inc_prefix[idx - k_usize]
                && dec_prefix[idx + k_usize] == dec_prefix[idx + 1]
            {
                proof {
                    assert(Self::good_index(nums@, k as int, idx as int)) by {
                        assert(1 <= k as int);
                        assert((k as int) <= (idx as int));
                        assert((idx as int) + (k as int) < (n as int));
                        assert forall |j: int| (idx as int) - (k as int) <= j < (idx as int) - 1 implies #[trigger] nums[j] >= nums[j + 1] by {
                            if nums[j] < nums[j + 1] {
                                Self::lemma_inc_bad_prefix_monotonic(nums@, (idx as int) - (k as int), j);
                                Self::lemma_inc_bad_prefix_monotonic(nums@, j + 1, (idx as int) - 1);
                                assert(Self::inc_bad_step(nums@, j) == 1);
                                assert(Self::inc_bad_prefix(nums@, j + 1) == Self::inc_bad_prefix(nums@, j) + Self::inc_bad_step(nums@, j));
                                assert(Self::inc_bad_prefix(nums@, (idx as int) - (k as int)) <= Self::inc_bad_prefix(nums@, j));
                                assert(Self::inc_bad_prefix(nums@, j + 1) <= Self::inc_bad_prefix(nums@, (idx as int) - 1));
                                assert(Self::inc_bad_prefix(nums@, (idx as int) - (k as int)) < Self::inc_bad_prefix(nums@, (idx as int) - 1));
                                assert(inc_prefix[(idx as int) - (k as int)] as int == Self::inc_bad_prefix(nums@, (idx as int) - (k as int)));
                                assert(inc_prefix[(idx as int) - 1] as int == Self::inc_bad_prefix(nums@, (idx as int) - 1));
                                assert(false);
                            }
                        }
                        assert forall |j: int| (idx as int) + 1 <= j < (idx as int) + (k as int) implies #[trigger] nums[j] <= nums[j + 1] by {
                            if nums[j] > nums[j + 1] {
                                Self::lemma_dec_bad_prefix_monotonic(nums@, (idx as int) + 1, j);
                                Self::lemma_dec_bad_prefix_monotonic(nums@, j + 1, (idx as int) + (k as int));
                                assert(Self::dec_bad_step(nums@, j) == 1);
                                assert(Self::dec_bad_prefix(nums@, j + 1) == Self::dec_bad_prefix(nums@, j) + Self::dec_bad_step(nums@, j));
                                assert(Self::dec_bad_prefix(nums@, (idx as int) + 1) <= Self::dec_bad_prefix(nums@, j));
                                assert(Self::dec_bad_prefix(nums@, j + 1) <= Self::dec_bad_prefix(nums@, (idx as int) + (k as int)));
                                assert(Self::dec_bad_prefix(nums@, (idx as int) + 1) < Self::dec_bad_prefix(nums@, (idx as int) + (k as int)));
                                assert(dec_prefix[(idx as int) + 1] as int == Self::dec_bad_prefix(nums@, (idx as int) + 1));
                                assert(dec_prefix[(idx as int) + (k as int)] as int == Self::dec_bad_prefix(nums@, (idx as int) + (k as int)));
                                assert(false);
                            }
                        }
                    }
                }
                let ghost old_result = result@;
                result.push(idx_i);
                proof {
                    assert(result@ == old_result.push(idx_i));
                    assert forall |x: i32| #[trigger] old_result.contains(x) implies result@.contains(x) by {
                        if old_result.contains(x) {
                            let p = choose |p: int| 0 <= p < old_result.len() && old_result[p] == x;
                            assert(0 <= p < result@.len());
                            assert(result@[p] == x);
                        }
                    }
                    assert(result@[result@.len() - 1] == idx_i);
                    assert(result@.contains(idx_i));
                    assert forall |m: int| 0 <= m < result@.len() implies
                        0 <= result@[m] < idx as i32 + 1
                        && Self::good_index(nums@, k as int, result@[m] as int) by {
                        if m < old_result.len() {
                            assert(result@[m] == old_result[m]);
                        } else {
                            assert(m == old_result.len());
                        }
                    }
                    assert forall |cand: int|
                        k as int <= cand < idx as int + 1
                        && cand + (k as int) < (n as int)
                        && inc_prefix[cand - 1] == inc_prefix[cand - (k as int)]
                        && dec_prefix[cand + (k as int)] == dec_prefix[cand + 1]
                        implies #[trigger] result@.contains(cand as i32) by {
                        if cand < idx as int {
                            assert(old_result.contains(cand as i32));
                            assert(result@.contains(cand as i32));
                        } else {
                            assert(cand == idx as int);
                            assert(result@.contains(idx_i));
                        }
                    }
                    assert forall |a: int, b: int| 0 <= a < b < result@.len() implies result@[a] < result@[b] by {
                        if b < old_result.len() {
                            assert(result@[a] == old_result[a]);
                            assert(result@[b] == old_result[b]);
                        } else {
                            assert(b == old_result.len());
                            assert(result@[b] == idx_i);
                            assert(result@[a] == old_result[a]);
                            assert(old_result[a] < idx_i);
                        }
                    }
                }
            }
            idx += 1;
        }

        proof {
            assert forall |cand: int| 0 <= cand < nums.len() && Self::good_index(nums@, k as int, cand)
                implies #[trigger] result@.contains(cand as i32) by {
                if Self::inc_bad_prefix(nums@, cand - (k as int)) < Self::inc_bad_prefix(nums@, cand - 1) {
                    Self::lemma_inc_bad_prefix_difference_has_bad(nums@, cand - (k as int), cand - 1);
                    let m = choose |m: int| cand - (k as int) <= m < cand - 1 && Self::inc_bad_step(nums@, m) == 1;
                    assert(cand - (k as int) <= m < cand - 1 && Self::inc_bad_step(nums@, m) == 1);
                    assert(nums[m] < nums[m + 1]);
                    assert(false);
                }
                Self::lemma_inc_bad_prefix_monotonic(nums@, cand - (k as int), cand - 1);
                assert(Self::inc_bad_prefix(nums@, cand - (k as int)) == Self::inc_bad_prefix(nums@, cand - 1));
                if Self::dec_bad_prefix(nums@, cand + 1) < Self::dec_bad_prefix(nums@, cand + (k as int)) {
                    Self::lemma_dec_bad_prefix_difference_has_bad(nums@, cand + 1, cand + (k as int));
                    let m = choose |m: int| cand + 1 <= m < cand + (k as int) && Self::dec_bad_step(nums@, m) == 1;
                    assert(cand + 1 <= m < cand + (k as int) && Self::dec_bad_step(nums@, m) == 1);
                    assert(nums[m] > nums[m + 1]);
                    assert(false);
                }
                Self::lemma_dec_bad_prefix_monotonic(nums@, cand + 1, cand + (k as int));
                assert(Self::dec_bad_prefix(nums@, cand + 1) == Self::dec_bad_prefix(nums@, cand + (k as int)));
                assert(inc_prefix[cand - 1] as int == Self::inc_bad_prefix(nums@, cand - 1));
                assert(inc_prefix[cand - (k as int)] as int == Self::inc_bad_prefix(nums@, cand - (k as int)));
                assert(dec_prefix[cand + 1] as int == Self::dec_bad_prefix(nums@, cand + 1));
                assert(dec_prefix[cand + (k as int)] as int == Self::dec_bad_prefix(nums@, cand + (k as int)));
            }
        }

        result
    }
}

}
