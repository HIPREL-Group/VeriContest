use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn distinct(seq: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> #[trigger] seq[i] != #[trigger] seq[j]
}

pub open spec fn reversed_value(seq: Seq<i64>, l: int, r: int, i: int) -> i64
    recommends
        0 <= l <= r < seq.len(),
        0 <= i < seq.len(),
{
    if l <= i && i <= r {
        seq[l + r - i]
    } else {
        seq[i]
    }
}

pub open spec fn reversal_sorts(seq: Seq<i64>, l: int, r: int) -> bool
    recommends
        0 <= l <= r < seq.len(),
{
    forall|i: int| 0 <= i < seq.len() - 1 ==> #[trigger] reversed_value(seq, l, r, i) <= reversed_value(seq, l, r, i + 1)
}

pub open spec fn exists_sorting_segment(seq: Seq<i64>) -> bool {
    exists|l: int, r: int| 0 <= l <= r < seq.len() && reversal_sorts(seq, l, r)
}

proof fn lemma_reversal_sorts_implies_reversed_segment_descends(seq: Seq<i64>, l: int, r: int, p: int)
    requires
        0 <= l <= p < r < seq.len(),
        reversal_sorts(seq, l, r),
    ensures
        seq[p + 1] <= seq[p],
{
    let q = l + (r - (p + 1));
    assert(0 <= r - (p + 1));
    assert(0 <= q);
    assert(l <= q);
    assert(r - q == p + 1 - l);
    assert(1 <= p + 1 - l);
    assert(q < r);
    assert(0 <= q);
    assert(q + 1 <= r);
    assert(q < seq.len() - 1);
    assert(l + r - q == p + 1);
    assert(l + r - (q + 1) == p);
    assert(reversed_value(seq, l, r, q) == seq[p + 1]);
    assert(reversed_value(seq, l, r, q + 1) == seq[p]);
    assert(reversed_value(seq, l, r, q) <= reversed_value(seq, l, r, q + 1));
}

proof fn lemma_reversal_sorts_implies_segment_nonincreasing(seq: Seq<i64>, l: int, r: int, i: int, j: int)
    requires
        0 <= l <= i <= j <= r < seq.len(),
        reversal_sorts(seq, l, r),
    ensures
        seq[i] >= seq[j],
    decreases j - i,
{
    if i < j {
        lemma_reversal_sorts_implies_reversed_segment_descends(seq, l, r, i);
        lemma_reversal_sorts_implies_segment_nonincreasing(seq, l, r, i + 1, j);
    }
}

proof fn lemma_reversal_sorts_implies_segment_inversion(seq: Seq<i64>, l: int, r: int, i: int, j: int)
    requires
        0 <= l <= i < j <= r < seq.len(),
        reversal_sorts(seq, l, r),
        distinct(seq),
    ensures
        seq[i] > seq[j],
{
    lemma_reversal_sorts_implies_segment_nonincreasing(seq, l, r, i, j);
    assert(seq[i] != seq[j]);
    assert(seq[i] > seq[j]);
}

proof fn lemma_sorting_segment_matches_candidate(seq: Seq<i64>, left: int, right: int, l: int, r: int)
    requires
        1 <= seq.len(),
        distinct(seq),
        0 <= left < right < seq.len(),
        seq[left] > seq[left + 1],
        forall|i: int| 0 <= i < left ==> #[trigger] seq[i] <= seq[i + 1],
        seq[right - 1] > seq[right],
        forall|i: int| right <= i < seq.len() - 1 ==> #[trigger] seq[i] <= seq[i + 1],
        0 <= l <= r < seq.len(),
        reversal_sorts(seq, l, r),
    ensures
        l == left,
        r == right,
{
    if l < left {
        lemma_reversal_sorts_implies_segment_inversion(seq, l, r, l, l + 1);
        assert(seq[l] <= seq[l + 1]);
        assert(false);
    }
    if left < l {
        if left + 1 < l {
            assert(reversed_value(seq, l, r, left) == seq[left]);
            assert(reversed_value(seq, l, r, left + 1) == seq[left + 1]);
            assert(reversed_value(seq, l, r, left) <= reversed_value(seq, l, r, left + 1));
            assert(false);
        } else {
            assert(l == left + 1);
            assert(reversed_value(seq, l, r, left) == seq[left]);
            assert(reversed_value(seq, l, r, left + 1) == seq[r]);
            assert(reversed_value(seq, l, r, left) <= reversed_value(seq, l, r, left + 1));
            if l < r {
                lemma_reversal_sorts_implies_segment_inversion(seq, l, r, l, r);
                assert(seq[left] > seq[l]);
                assert(seq[l] > seq[r]);
                assert(false);
            } else {
                assert(l == r);
                assert(seq[left] > seq[l]);
                assert(false);
            }
        }
    }
    if r > right {
        lemma_reversal_sorts_implies_segment_inversion(seq, l, r, right, right + 1);
        assert(seq[right] <= seq[right + 1]);
        assert(false);
    }
    if right > r {
        if r + 1 < right {
            assert(reversed_value(seq, l, r, right - 1) == seq[right - 1]);
            assert(reversed_value(seq, l, r, right) == seq[right]);
            assert(reversed_value(seq, l, r, right - 1) <= reversed_value(seq, l, r, right));
            assert(false);
        } else {
            assert(right == r + 1);
            assert(reversed_value(seq, l, r, r) == seq[l]);
            assert(reversed_value(seq, l, r, r + 1) == seq[right]);
            assert(reversed_value(seq, l, r, r) <= reversed_value(seq, l, r, r + 1));
            if l < r {
                lemma_reversal_sorts_implies_segment_inversion(seq, l, r, l, r);
                assert(seq[l] > seq[r]);
                assert(seq[r] > seq[right]);
                assert(false);
            } else {
                assert(l == r);
                assert(seq[r] > seq[right]);
                assert(false);
            }
        }
    }
    assert(l == left) by (nonlinear_arith)
        requires
            l <= left,
            l >= left;
    assert(r == right) by (nonlinear_arith)
        requires
            r <= right,
            r >= right;
}

impl Solution {
    pub fn sort_the_array(nums: Vec<i64>) -> (result: Option<(usize, usize)>)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
            distinct(nums@),
        ensures
            result != None::<(usize, usize)> ==> {
                let seg = result.get_Some_0();
                1 <= seg.0 <= seg.1 <= nums.len()
                    && reversal_sorts(nums@, seg.0 as int - 1, seg.1 as int - 1)
            },
            result == None::<(usize, usize)> ==> !exists_sorting_segment(nums@),
    {
        let n = nums.len();
        if n == 1 {
            proof {
                assert(reversal_sorts(nums@, 0, 0)) by {
                    assert forall|i: int| 0 <= i < nums@.len() - 1 implies #[trigger] reversed_value(nums@, 0, 0, i) <= reversed_value(nums@, 0, 0, i + 1) by {
                    }
                };
            }
            return Some((1, 1));
        }

        let mut left = 0usize;
        while left + 1 < n && nums[left] <= nums[left + 1]
            invariant
                n == nums.len(),
                2 <= n <= 100_000,
                forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
                distinct(nums@),
                0 <= left < n,
                forall|i: int| 0 <= i < left as int ==> #[trigger] nums[i] <= nums[i + 1],
            decreases n - 1 - left,
        {
            left += 1;
        }

        if left + 1 == n {
            proof {
                assert(left == n - 1);
                assert(reversal_sorts(nums@, 0, 0)) by {
                    assert forall|i: int| 0 <= i < nums@.len() - 1 implies #[trigger] reversed_value(nums@, 0, 0, i) <= reversed_value(nums@, 0, 0, i + 1) by {
                        assert(i < left as int);
                        assert(nums[i] <= nums[i + 1]);
                        assert(reversed_value(nums@, 0, 0, i) == nums@[i]);
                        assert(reversed_value(nums@, 0, 0, i + 1) == nums@[i + 1]);
                    }
                };
            }
            return Some((1, 1));
        }

        proof {
            assert(left + 1 < n);
            assert(nums[left as int] > nums[left as int + 1]);
        }

        let mut right = n - 1;
        while right > 0 && nums[right - 1] <= nums[right]
            invariant
                n == nums.len(),
                2 <= n <= 100_000,
                forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
                distinct(nums@),
                0 <= left < n - 1,
                nums[left as int] > nums[left as int + 1],
                forall|i: int| 0 <= i < left as int ==> #[trigger] nums[i] <= nums[i + 1],
                0 < right < n,
                forall|i: int| right as int <= i < nums.len() - 1 ==> #[trigger] nums[i] <= nums[i + 1],
            decreases right,
        {
            right -= 1;
        }

        proof {
            assert(right > 0);
            assert(nums[right as int - 1] > nums[right as int]);
            if right <= left {
                assert(right as int <= left as int);
                assert(left + 1 < nums.len());
                assert(nums[left as int] <= nums[left as int + 1]);
                assert(false);
            }
            assert(left < right);
        }

        let mut i = 0usize;
        while i + 1 < n
            invariant
                n == nums.len(),
                2 <= n <= 100_000,
                forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1_000_000_000,
                distinct(nums@),
                0 <= left < right < n,
                nums[left as int] > nums[left as int + 1],
                forall|k: int| 0 <= k < left as int ==> #[trigger] nums[k] <= nums[k + 1],
                nums[right as int - 1] > nums[right as int],
                forall|k: int| right as int <= k < nums.len() - 1 ==> #[trigger] nums[k] <= nums[k + 1],
                0 <= i < n,
                forall|k: int| 0 <= k < i as int ==> #[trigger] reversed_value(nums@, left as int, right as int, k) <= reversed_value(nums@, left as int, right as int, k + 1),
            decreases n - 1 - i,
        {
            let a = if left <= i && i <= right {
                nums[right - (i - left)]
            } else {
                nums[i]
            };
            let j = i + 1;
            let b = if left <= j && j <= right {
                nums[right - (j - left)]
            } else {
                nums[j]
            };
            if a > b {
                proof {
                    if left <= i && i <= right {
                        assert(a == nums[right - (i - left)]);
                        assert((right - (i - left)) as int == right as int - (i as int - left as int));
                        assert((right - (i - left)) as int == left as int + right as int - i as int) by (nonlinear_arith)
                            requires
                                left <= i <= right;
                        assert(a == reversed_value(nums@, left as int, right as int, i as int));
                    } else {
                        assert(a == nums[i as int]);
                        assert(a == reversed_value(nums@, left as int, right as int, i as int));
                    }
                    if left <= j && j <= right {
                        assert(b == nums[right - (j - left)]);
                        assert((right - (j - left)) as int == right as int - (j as int - left as int));
                        assert((right - (j - left)) as int == left as int + right as int - j as int) by (nonlinear_arith)
                            requires
                                left <= j <= right;
                        assert(b == reversed_value(nums@, left as int, right as int, j as int));
                    } else {
                        assert(b == nums[j as int]);
                        assert(b == reversed_value(nums@, left as int, right as int, j as int));
                    }
                    if exists_sorting_segment(nums@) {
                        let witness = choose|l: int, r: int| 0 <= l <= r < nums@.len() && reversal_sorts(nums@, l, r);
                        lemma_sorting_segment_matches_candidate(nums@, left as int, right as int, witness.0, witness.1);
                        assert(witness.0 == left as int);
                        assert(witness.1 == right as int);
                        assert(reversal_sorts(nums@, left as int, right as int));
                        assert(reversed_value(nums@, left as int, right as int, i as int) <= reversed_value(nums@, left as int, right as int, j as int));
                        assert(false);
                    }
                }
                return None;
            }
            i += 1;
        }

        proof {
            assert(i == n - 1);
            assert(reversal_sorts(nums@, left as int, right as int)) by {
                assert forall|k: int| 0 <= k < nums@.len() - 1 implies #[trigger] reversed_value(nums@, left as int, right as int, k) <= reversed_value(nums@, left as int, right as int, k + 1) by {
                    assert(k < i as int);
                }
            };
        }
        Some((left + 1, right + 1))
    }
}

}
