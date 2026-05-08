use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

pub open spec fn is_minimum(nums: Seq<i64>, mn: int) -> bool {
    nums.len() > 0
        && exists|i: int| 0 <= i < nums.len() && nums[i] as int == mn
        && forall|j: int| 0 <= j < nums.len() ==> mn <= #[trigger] nums[j] as int
}

pub open spec fn is_maximum(nums: Seq<i64>, mx: int) -> bool {
    nums.len() > 0
        && exists|i: int| 0 <= i < nums.len() && nums[i] as int == mx
        && forall|j: int| 0 <= j < nums.len() ==> #[trigger] nums[j] as int <= mx
}

pub open spec fn count_value_up_to(nums: Seq<i64>, value: int, end: int) -> nat
    recommends 0 <= end <= nums.len(),
    decreases end,
{
    if end <= 0 {
        0
    } else {
        count_value_up_to(nums, value, end - 1)
            + if nums[end - 1] as int == value { 1nat } else { 0nat }
    }
}

pub open spec fn count_value(nums: Seq<i64>, value: int) -> nat {
    count_value_up_to(nums, value, nums.len() as int)
}

pub open spec fn is_extremal_pair_for(nums: Seq<i64>, mn: int, mx: int, i: int, j: int) -> bool {
    &&& 0 <= i < j < nums.len()
    &&& (
        (nums[i] as int == mn && nums[j] as int == mx)
        || (nums[i] as int == mx && nums[j] as int == mn)
    )
}

pub open spec fn count_extremal_pairs_for_with_right(nums: Seq<i64>, mn: int, mx: int, right: int, left_end: int) -> nat
    recommends 0 <= left_end <= right < nums.len(),
    decreases left_end,
{
    if left_end <= 0 {
        0
    } else {
        count_extremal_pairs_for_with_right(nums, mn, mx, right, left_end - 1)
            + if is_extremal_pair_for(nums, mn, mx, left_end - 1, right) { 1nat } else { 0nat }
    }
}

pub open spec fn count_extremal_pairs_for_up_to(nums: Seq<i64>, mn: int, mx: int, end: int) -> nat
    recommends 0 <= end <= nums.len(),
    decreases end,
{
    if end <= 1 {
        0
    } else {
        count_extremal_pairs_for_up_to(nums, mn, mx, end - 1)
            + count_extremal_pairs_for_with_right(nums, mn, mx, end - 1, end - 1)
    }
}

pub open spec fn choose2(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        choose2((n - 1) as nat) + ((n - 1) as nat)
    }
}

proof fn lemma_choose2_closed_form(n: nat)
    ensures
        choose2(n) == n * (n - 1) / 2,
    decreases n,
{
    if n == 0 {
    } else {
        lemma_choose2_closed_form((n - 1) as nat);
        assert(choose2(n) == choose2((n - 1) as nat) + (n - 1));
        assert((((n - 1) * (n - 2)) / 2) + (n - 1) == (n * (n - 1)) / 2) by (nonlinear_arith);
    }
}

proof fn lemma_count_value_zero_when_absent(nums: Seq<i64>, value: int, end: int)
    requires
        0 <= end <= nums.len(),
        forall|i: int| 0 <= i < end ==> nums[i] as int != value,
    ensures
        count_value_up_to(nums, value, end) == 0,
    decreases end,
{
    if end <= 0 {
    } else {
        lemma_count_value_zero_when_absent(nums, value, end - 1);
        assert(nums[end - 1] as int != value);
    }
}

proof fn lemma_all_equal_from_min_max(nums: Seq<i64>, mn: int, mx: int)
    requires
        is_minimum(nums, mn),
        is_maximum(nums, mx),
        mn == mx,
    ensures
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] as int == mn,
{
    assert forall|i: int| 0 <= i < nums.len() implies #[trigger] nums[i] as int == mn by {
        assert(mn <= nums[i] as int);
        assert(nums[i] as int <= mx);
    }
}

proof fn lemma_count_pairs_with_right_all_equal(nums: Seq<i64>, mn: int, right: int, left_end: int)
    requires
        0 <= left_end <= right < nums.len(),
        forall|i: int| 0 <= i <= right ==> nums[i] as int == mn,
    ensures
        count_extremal_pairs_for_with_right(nums, mn, mn, right, left_end) == left_end,
    decreases left_end,
{
    if left_end <= 0 {
    } else {
        lemma_count_pairs_with_right_all_equal(nums, mn, right, left_end - 1);
        assert(is_extremal_pair_for(nums, mn, mn, left_end - 1, right));
    }
}

proof fn lemma_choose2_base(n: nat)
    requires n <= 1,
    ensures choose2(n) == 0,
{
    reveal_with_fuel(choose2, 2);
}

proof fn lemma_count_pairs_all_equal(nums: Seq<i64>, mn: int, end: int)
    requires
        0 <= end <= nums.len(),
        forall|i: int| 0 <= i < end ==> nums[i] as int == mn,
    ensures
        count_extremal_pairs_for_up_to(nums, mn, mn, end) == choose2(end as nat),
    decreases end,
{
    if end <= 1 {
        assert(count_extremal_pairs_for_up_to(nums, mn, mn, end) == 0);
        lemma_choose2_base(end as nat);
    } else {
        lemma_count_pairs_all_equal(nums, mn, end - 1);
        lemma_count_pairs_with_right_all_equal(nums, mn, end - 1, end - 1);
        assert(count_extremal_pairs_for_up_to(nums, mn, mn, end - 1) == choose2((end - 1) as nat));
        assert(count_extremal_pairs_for_with_right(nums, mn, mn, end - 1, end - 1) == (end - 1) as nat);
        assert(count_extremal_pairs_for_up_to(nums, mn, mn, end)
            == count_extremal_pairs_for_up_to(nums, mn, mn, end - 1)
                + count_extremal_pairs_for_with_right(nums, mn, mn, end - 1, end - 1));
        assert(choose2(end as nat) == choose2((end - 1) as nat) + ((end - 1) as nat));
        assert(count_extremal_pairs_for_up_to(nums, mn, mn, end)
            == choose2((end - 1) as nat) + ((end - 1) as nat));
    }
}

proof fn lemma_count_pairs_with_right_distinct(nums: Seq<i64>, mn: int, mx: int, right: int, left_end: int)
    requires
        0 <= left_end <= right < nums.len(),
        mn < mx,
        forall|i: int| 0 <= i <= right ==> mn <= #[trigger] nums[i] as int && nums[i] as int <= mx,
    ensures
        nums[right] as int == mn ==> count_extremal_pairs_for_with_right(nums, mn, mx, right, left_end) == count_value_up_to(nums, mx, left_end),
        nums[right] as int == mx ==> count_extremal_pairs_for_with_right(nums, mn, mx, right, left_end) == count_value_up_to(nums, mn, left_end),
        nums[right] as int != mn && nums[right] as int != mx ==> count_extremal_pairs_for_with_right(nums, mn, mx, right, left_end) == 0,
    decreases left_end,
{
    if left_end <= 0 {
    } else {
        lemma_count_pairs_with_right_distinct(nums, mn, mx, right, left_end - 1);
        if nums[right] as int == mn {
            assert(nums[right] as int != mx);
            assert(is_extremal_pair_for(nums, mn, mx, left_end - 1, right) <==> nums[left_end - 1] as int == mx);
        } else if nums[right] as int == mx {
            assert(nums[right] as int != mn);
            assert(is_extremal_pair_for(nums, mn, mx, left_end - 1, right) <==> nums[left_end - 1] as int == mn);
        } else {
            assert(!is_extremal_pair_for(nums, mn, mx, left_end - 1, right));
        }
    }
}

proof fn lemma_count_pairs_distinct(nums: Seq<i64>, mn: int, mx: int, end: int)
    requires
        0 <= end <= nums.len(),
        mn < mx,
        forall|i: int| 0 <= i < end ==> mn <= #[trigger] nums[i] as int && nums[i] as int <= mx,
    ensures
        count_extremal_pairs_for_up_to(nums, mn, mx, end)
            == count_value_up_to(nums, mn, end) * count_value_up_to(nums, mx, end),
    decreases end,
{
    if end <= 1 {
    } else {
        lemma_count_pairs_distinct(nums, mn, mx, end - 1);
        lemma_count_pairs_with_right_distinct(nums, mn, mx, end - 1, end - 1);
        if nums[end - 1] as int == mn {
            assert(count_value_up_to(nums, mn, end) == count_value_up_to(nums, mn, end - 1) + 1);
            assert(count_value_up_to(nums, mx, end) == count_value_up_to(nums, mx, end - 1));
            assert(count_extremal_pairs_for_up_to(nums, mn, mx, end)
                == count_extremal_pairs_for_up_to(nums, mn, mx, end - 1)
                    + count_value_up_to(nums, mx, end - 1));
            assert(count_value_up_to(nums, mn, end - 1) * count_value_up_to(nums, mx, end - 1)
                + count_value_up_to(nums, mx, end - 1)
                == (count_value_up_to(nums, mn, end - 1) + 1) * count_value_up_to(nums, mx, end - 1)) by (nonlinear_arith);
        } else if nums[end - 1] as int == mx {
            assert(count_value_up_to(nums, mn, end) == count_value_up_to(nums, mn, end - 1));
            assert(count_value_up_to(nums, mx, end) == count_value_up_to(nums, mx, end - 1) + 1);
            assert(count_extremal_pairs_for_up_to(nums, mn, mx, end)
                == count_extremal_pairs_for_up_to(nums, mn, mx, end - 1)
                    + count_value_up_to(nums, mn, end - 1));
            assert(count_value_up_to(nums, mn, end - 1) * count_value_up_to(nums, mx, end - 1)
                + count_value_up_to(nums, mn, end - 1)
                == count_value_up_to(nums, mn, end - 1) * (count_value_up_to(nums, mx, end - 1) + 1)) by (nonlinear_arith);
        } else {
            assert(count_value_up_to(nums, mn, end) == count_value_up_to(nums, mn, end - 1));
            assert(count_value_up_to(nums, mx, end) == count_value_up_to(nums, mx, end - 1));
            assert(count_extremal_pairs_for_up_to(nums, mn, mx, end)
                == count_extremal_pairs_for_up_to(nums, mn, mx, end - 1));
        }
    }
}

proof fn lemma_extremal_pair_matches_max_difference(nums: Seq<i64>, mn: int, mx: int, i: int, j: int)
    requires
        is_minimum(nums, mn),
        is_maximum(nums, mx),
        0 <= i < j < nums.len(),
    ensures
        is_extremal_pair_for(nums, mn, mx, i, j) <==> abs_diff(nums[i] as int, nums[j] as int) == mx - mn,
{
    let a = nums[i] as int;
    let b = nums[j] as int;
    assert(mn <= a);
    assert(a <= mx);
    assert(mn <= b);
    assert(b <= mx);
    if is_extremal_pair_for(nums, mn, mx, i, j) {
        if a == mn && b == mx {
            assert(abs_diff(a, b) == mx - mn);
        } else {
            assert(a == mx && b == mn);
            assert(abs_diff(a, b) == mx - mn);
        }
    } else {
        if a >= b {
            assert(abs_diff(a, b) == a - b);
            if abs_diff(a, b) == mx - mn {
                assert((mx - a) + (b - mn) == (mx - mn) - (a - b));
                assert(mx - a == 0);
                assert(b - mn == 0);
                assert(a == mx && b == mn);
                assert(is_extremal_pair_for(nums, mn, mx, i, j));
            }
        } else {
            assert(abs_diff(a, b) == b - a);
            if abs_diff(a, b) == mx - mn {
                assert((mx - b) + (a - mn) == (mx - mn) - (b - a));
                assert(mx - b == 0);
                assert(a - mn == 0);
                assert(a == mn && b == mx);
                assert(is_extremal_pair_for(nums, mn, mx, i, j));
            }
        }
    }
}

impl Solution {
    pub fn max_beauty_and_pair_count(flowers: Vec<i64>) -> (result: (i64, i64))
        requires
            2 <= flowers.len() <= 200_000,
            forall|i: int| 0 <= i < flowers.len() ==> 1 <= #[trigger] flowers[i] <= 1_000_000_000,
        ensures
            exists|mn: int, mx: int| {
                &&& is_minimum(flowers@, mn)
                &&& is_maximum(flowers@, mx)
                &&& result.0 as int == mx - mn
                &&& result.1 as int == count_extremal_pairs_for_up_to(flowers@, mn, mx, flowers.len() as int)
                &&& forall|i: int, j: int|
                    0 <= i < j < flowers.len() ==> (
                        #[trigger] is_extremal_pair_for(flowers@, mn, mx, i, j)
                        <==> abs_diff(flowers[i] as int, flowers[j] as int) == result.0 as int
                    )
            },
    {
        let mut min_val = flowers[0];
        let mut max_val = flowers[0];
        let mut min_count = 1i64;
        let mut max_count = 1i64;
        let mut i = 1usize;
        proof {
            assert(1 <= flowers[0] <= 1_000_000_000);
            reveal_with_fuel(count_value_up_to, 2);
            assert(count_value_up_to(flowers@, min_val as int, 1) == 1);
            assert(count_value_up_to(flowers@, max_val as int, 1) == 1);
        }
        while i < flowers.len()
            invariant
                1 <= i <= flowers.len(),
                1 <= min_count <= i as int,
                1 <= max_count <= i as int,
                flowers.len() <= 200_000,
                exists|k: int| 0 <= k < i as int && flowers[k] == min_val,
                exists|k: int| 0 <= k < i as int && flowers[k] == max_val,
                forall|k: int| 0 <= k < i as int ==> min_val <= #[trigger] flowers[k],
                forall|k: int| 0 <= k < i as int ==> #[trigger] flowers[k] <= max_val,
                min_count as int == count_value_up_to(flowers@, min_val as int, i as int),
                max_count as int == count_value_up_to(flowers@, max_val as int, i as int),
            decreases flowers.len() - i,
        {
            let x = flowers[i];
            let ghost old_i = i as int;
            let ghost old_min = min_val as int;
            let ghost old_max = max_val as int;
            let ghost old_min_count = min_count as int;
            let ghost old_max_count = max_count as int;
            if x < min_val {
                min_val = x;
                min_count = 1;
            } else if x == min_val {
                assert(min_count as int <= i as int);
                assert((i as int) < flowers.len() as int);
                assert(flowers.len() as int <= 200_000);
                min_count += 1;
            }
            if x > max_val {
                max_val = x;
                max_count = 1;
            } else if x == max_val {
                assert(max_count as int <= i as int);
                assert((i as int) < flowers.len() as int);
                assert(flowers.len() as int <= 200_000);
                max_count += 1;
            }
            proof {
                if x < old_min as i64 {
                    assert forall|k: int| 0 <= k < old_i implies flowers[k] as int != x as int by {
                        assert(old_min <= flowers[k] as int);
                    }
                    lemma_count_value_zero_when_absent(flowers@, x as int, old_i);
                    assert(count_value_up_to(flowers@, x as int, old_i + 1) == 1);
                } else if x == old_min as i64 {
                    assert(count_value_up_to(flowers@, old_min, old_i + 1) == old_min_count + 1);
                } else {
                    assert(x as int != old_min);
                    assert(count_value_up_to(flowers@, old_min, old_i + 1) == old_min_count);
                }
                if x > old_max as i64 {
                    assert forall|k: int| 0 <= k < old_i implies flowers[k] as int != x as int by {
                        assert(flowers[k] as int <= old_max);
                    }
                    lemma_count_value_zero_when_absent(flowers@, x as int, old_i);
                    assert(count_value_up_to(flowers@, x as int, old_i + 1) == 1);
                } else if x == old_max as i64 {
                    assert(count_value_up_to(flowers@, old_max, old_i + 1) == old_max_count + 1);
                } else {
                    assert(x as int != old_max);
                    assert(count_value_up_to(flowers@, old_max, old_i + 1) == old_max_count);
                }
                if x < old_min as i64 {
                    assert(min_val as int == x as int);
                    assert(min_count as int == 1);
                    assert(exists|k: int| 0 <= k < old_i + 1 && flowers[k] == min_val);
                    assert forall|k: int| 0 <= k < old_i + 1 implies min_val <= #[trigger] flowers[k] by {
                        if k < old_i {
                            assert(old_min <= flowers[k] as int);
                        }
                    }
                } else {
                    assert(min_val as int == old_min);
                    assert(exists|k: int| 0 <= k < old_i + 1 && flowers[k] == min_val);
                    assert forall|k: int| 0 <= k < old_i + 1 implies min_val <= #[trigger] flowers[k] by {
                        if k < old_i {
                            assert(old_min <= flowers[k] as int);
                        }
                    }
                }
                if x > old_max as i64 {
                    assert(max_val as int == x as int);
                    assert(max_count as int == 1);
                    assert(exists|k: int| 0 <= k < old_i + 1 && flowers[k] == max_val);
                    assert forall|k: int| 0 <= k < old_i + 1 implies #[trigger] flowers[k] <= max_val by {
                        if k < old_i {
                            assert(flowers[k] as int <= old_max);
                        }
                    }
                } else {
                    assert(max_val as int == old_max);
                    assert(exists|k: int| 0 <= k < old_i + 1 && flowers[k] == max_val);
                    assert forall|k: int| 0 <= k < old_i + 1 implies #[trigger] flowers[k] <= max_val by {
                        if k < old_i {
                            assert(flowers[k] as int <= old_max);
                        }
                    }
                }
            }
            i += 1;
        }
        proof {
            assert(i == flowers.len());
        }
        let diff = max_val - min_val;
        let n = flowers.len() as i64;
        proof {
            let len = flowers.len() as int;
            let mc = min_count as int;
            let xc = max_count as int;
            assert(mc <= len);
            assert(xc <= len);
            assert(len <= 200_000);
            assert(len * len <= 200_000 * 200_000) by (nonlinear_arith)
                requires 0 <= len <= 200_000;
            assert(mc * xc <= 200_000 * 200_000) by (nonlinear_arith)
                requires 0 <= mc <= 200_000, 0 <= xc <= 200_000;
            assert(200_000 * 200_000 < 9_223_372_036_854_775_807int);
            assert(n as int == len);
            assert(n as int <= 200_000);
            assert((n as int) * ((n as int) - 1) <= 200_000 * 199_999) by (nonlinear_arith)
                requires n as int <= 200_000, n as int >= 2;
            assert((n as int) * ((n as int) - 1) / 2 <= 200_000 * 199_999 / 2);
            assert(200_000 * 199_999 / 2 < 9_223_372_036_854_775_807int);
        }
        let pair_count = if min_val == max_val {
            n * (n - 1) / 2
        } else {
            min_count * max_count
        };
        proof {
            let mn = min_val as int;
            let mx = max_val as int;
            assert(is_minimum(flowers@, mn));
            assert(is_maximum(flowers@, mx));
            assert(diff as int == mx - mn);
            if min_val == max_val {
                lemma_all_equal_from_min_max(flowers@, mn, mx);
                lemma_count_pairs_all_equal(flowers@, mn, flowers.len() as int);
                lemma_choose2_closed_form(flowers.len() as nat);
                assert(count_extremal_pairs_for_up_to(flowers@, mn, mx, flowers.len() as int) == choose2(flowers.len() as nat));
                assert(pair_count as int == choose2(flowers.len() as nat));
            } else {
                assert(mn < mx);
                lemma_count_pairs_distinct(flowers@, mn, mx, flowers.len() as int);
                assert(count_extremal_pairs_for_up_to(flowers@, mn, mx, flowers.len() as int)
                    == count_value(flowers@, mn) * count_value(flowers@, mx));
                assert(pair_count as int == count_value(flowers@, mn) * count_value(flowers@, mx));
            }
            assert forall|a: int, b: int| 0 <= a < b < flowers.len() implies (
                #[trigger] is_extremal_pair_for(flowers@, mn, mx, a, b)
                <==> abs_diff(flowers[a] as int, flowers[b] as int) == diff as int
            ) by {
                lemma_extremal_pair_matches_max_difference(flowers@, mn, mx, a, b);
            }
            assert(exists|mn2: int, mx2: int| {
                &&& is_minimum(flowers@, mn2)
                &&& is_maximum(flowers@, mx2)
                &&& diff as int == mx2 - mn2
                &&& pair_count as int == count_extremal_pairs_for_up_to(flowers@, mn2, mx2, flowers.len() as int)
                &&& forall|a: int, b: int|
                    0 <= a < b < flowers.len() ==> (
                        #[trigger] is_extremal_pair_for(flowers@, mn2, mx2, a, b)
                        <==> abs_diff(flowers[a] as int, flowers[b] as int) == diff as int
                    )
            });
        }
        (diff, pair_count)
    }
}

}