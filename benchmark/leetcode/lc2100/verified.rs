use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn good_day(security: Seq<i32>, time: int, day: int) -> bool {
        0 <= day < security.len()
        && 0 <= time
        && time <= day
        && day + time < security.len()
        && (forall |j: int| day - time <= j < day ==> #[trigger] security[j] >= security[j + 1])
        && (forall |j: int| day <= j < day + time ==> #[trigger] security[j] <= security[j + 1])
    }

    pub open spec fn inc_bad_step(security: Seq<i32>, i: int) -> int
        recommends
            0 <= i + 1 < security.len(),
    {
        if security[i] < security[i + 1] { 1 } else { 0 }
    }

    pub open spec fn dec_bad_step(security: Seq<i32>, i: int) -> int
        recommends
            0 <= i + 1 < security.len(),
    {
        if security[i] > security[i + 1] { 1 } else { 0 }
    }

    pub open spec fn inc_bad_prefix(security: Seq<i32>, end: int) -> int
        recommends
            0 <= end < security.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::inc_bad_prefix(security, end - 1) + Self::inc_bad_step(security, end - 1)
        }
    }

    pub open spec fn dec_bad_prefix(security: Seq<i32>, end: int) -> int
        recommends
            0 <= end < security.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::dec_bad_prefix(security, end - 1) + Self::dec_bad_step(security, end - 1)
        }
    }

    proof fn lemma_inc_bad_prefix_monotonic(security: Seq<i32>, left: int, right: int)
        requires
            0 <= left <= right < security.len(),
        ensures
            Self::inc_bad_prefix(security, left) <= Self::inc_bad_prefix(security, right),
        decreases right - left,
    {
        if left < right {
            Self::lemma_inc_bad_prefix_monotonic(security, left, right - 1);
            assert(Self::inc_bad_prefix(security, right) == Self::inc_bad_prefix(security, right - 1) + Self::inc_bad_step(security, right - 1));
            assert(0 <= Self::inc_bad_step(security, right - 1));
        }
    }

    proof fn lemma_dec_bad_prefix_monotonic(security: Seq<i32>, left: int, right: int)
        requires
            0 <= left <= right < security.len(),
        ensures
            Self::dec_bad_prefix(security, left) <= Self::dec_bad_prefix(security, right),
        decreases right - left,
    {
        if left < right {
            Self::lemma_dec_bad_prefix_monotonic(security, left, right - 1);
            assert(Self::dec_bad_prefix(security, right) == Self::dec_bad_prefix(security, right - 1) + Self::dec_bad_step(security, right - 1));
            assert(0 <= Self::dec_bad_step(security, right - 1));
        }
    }

    proof fn lemma_inc_bad_prefix_difference_has_bad(security: Seq<i32>, left: int, right: int)
        requires
            0 <= left <= right < security.len(),
            Self::inc_bad_prefix(security, left) < Self::inc_bad_prefix(security, right),
        ensures
            exists |k: int| left <= k < right && #[trigger] Self::inc_bad_step(security, k) == 1,
        decreases right - left,
    {
        if left == right {
            assert(false);
        } else if Self::inc_bad_step(security, right - 1) == 1 {
            assert(left <= right - 1 < right);
        } else {
            assert(Self::inc_bad_prefix(security, right) == Self::inc_bad_prefix(security, right - 1));
            Self::lemma_inc_bad_prefix_difference_has_bad(security, left, right - 1);
        }
    }

    proof fn lemma_dec_bad_prefix_difference_has_bad(security: Seq<i32>, left: int, right: int)
        requires
            0 <= left <= right < security.len(),
            Self::dec_bad_prefix(security, left) < Self::dec_bad_prefix(security, right),
        ensures
            exists |k: int| left <= k < right && #[trigger] Self::dec_bad_step(security, k) == 1,
        decreases right - left,
    {
        if left == right {
            assert(false);
        } else if Self::dec_bad_step(security, right - 1) == 1 {
            assert(left <= right - 1 < right);
        } else {
            assert(Self::dec_bad_prefix(security, right) == Self::dec_bad_prefix(security, right - 1));
            Self::lemma_dec_bad_prefix_difference_has_bad(security, left, right - 1);
        }
    }

    pub fn good_days_to_rob_bank(security: Vec<i32>, time: i32) -> (result: Vec<i32>)
        requires
            1 <= security.len() <= 100_000,
            0 <= time <= 100_000,
            forall |i: int| 0 <= i < security.len() ==> 0 <= #[trigger] security[i] <= 100_000,
        ensures
            forall |k: int| 0 <= k < result@.len() ==>
                0 <= result@[k]
                && result@[k] < security.len() as i32
                && Self::good_day(security@, time as int, result@[k] as int),
            forall |day: int| 0 <= day < security.len() && Self::good_day(security@, time as int, day)
                ==> #[trigger] result@.contains(day as i32),
            forall |a: int, b: int| 0 <= a < b < result@.len() ==> result@[a] < result@[b],
    {
        let n = security.len();
        let mut inc_prefix: Vec<i32> = Vec::new();
        let mut dec_prefix: Vec<i32> = Vec::new();
        inc_prefix.push(0);
        dec_prefix.push(0);

        let mut i: usize = 1;
        while i < n
            invariant
                n == security.len(),
                1 <= n <= 100_000,
                1 <= i <= n,
                forall |k: int| 0 <= k < n ==> 0 <= #[trigger] security[k] <= 100_000,
                inc_prefix.len() == i,
                dec_prefix.len() == i,
                forall |k: int| 0 <= k < i as int ==> #[trigger] inc_prefix[k] as int == Self::inc_bad_prefix(security@, k),
                forall |k: int| 0 <= k < i as int ==> #[trigger] dec_prefix[k] as int == Self::dec_bad_prefix(security@, k),
                forall |k: int| 0 <= k < i as int ==> 0 <= #[trigger] inc_prefix[k] as int <= k,
                forall |k: int| 0 <= k < i as int ==> 0 <= #[trigger] dec_prefix[k] as int <= k,
            decreases n - i,
        {
            let mut inc_next = inc_prefix[i - 1];
            let prev = security[i - 1];
            let curr = security[i];
            if prev < curr {
                proof {
                    assert(0 <= inc_prefix[i as int - 1] as int <= i as int - 1);
                    assert(inc_next as int == inc_prefix[i as int - 1] as int);
                    assert(i as int - 1 < 2_147_483_647);
                    assert(inc_next < 2_147_483_647);
                }
                inc_next = inc_next + 1;
            }

            let mut dec_next = dec_prefix[i - 1];
            if prev > curr {
                dec_next = dec_next + 1;
            }

            let ghost old_inc = inc_prefix@;
            let ghost old_dec = dec_prefix@;
            inc_prefix.push(inc_next);
            dec_prefix.push(dec_next);
            proof {
                assert(inc_prefix@ == old_inc.push(inc_next));
                assert(dec_prefix@ == old_dec.push(dec_next));
                assert(Self::inc_bad_prefix(security@, i as int) == Self::inc_bad_prefix(security@, i as int - 1) + Self::inc_bad_step(security@, i as int - 1));
                assert(Self::dec_bad_prefix(security@, i as int) == Self::dec_bad_prefix(security@, i as int - 1) + Self::dec_bad_step(security@, i as int - 1));
                assert(inc_prefix[i as int - 1] as int == Self::inc_bad_prefix(security@, i as int - 1));
                assert(dec_prefix[i as int - 1] as int == Self::dec_bad_prefix(security@, i as int - 1));
                assert(prev == security[i as int - 1]);
                assert(curr == security[i as int]);
                if prev < curr {
                    assert(Self::inc_bad_step(security@, i as int - 1) == 1);
                    assert(inc_next as int == inc_prefix[i as int - 1] as int + 1);
                    assert(inc_next as int == Self::inc_bad_prefix(security@, i as int));
                } else {
                    assert(Self::inc_bad_step(security@, i as int - 1) == 0);
                    assert(inc_next as int == Self::inc_bad_prefix(security@, i as int));
                }
                if prev > curr {
                    assert(Self::dec_bad_step(security@, i as int - 1) == 1);
                    assert(dec_next as int == Self::dec_bad_prefix(security@, i as int));
                } else {
                    assert(Self::dec_bad_step(security@, i as int - 1) == 0);
                    assert(dec_next as int == Self::dec_bad_prefix(security@, i as int));
                }
                assert forall |k: int| 0 <= k < i as int + 1 implies #[trigger] inc_prefix[k] as int == Self::inc_bad_prefix(security@, k) by {
                    if k < i as int {
                        assert(inc_prefix@[k] == old_inc[k]);
                    } else {
                        assert(k == i as int);
                    }
                }
                assert forall |k: int| 0 <= k < i as int + 1 implies #[trigger] dec_prefix[k] as int == Self::dec_bad_prefix(security@, k) by {
                    if k < i as int {
                        assert(dec_prefix@[k] == old_dec[k]);
                    } else {
                        assert(k == i as int);
                    }
                }
                assert forall |k: int| 0 <= k < i as int + 1 implies 0 <= #[trigger] inc_prefix[k] as int <= k by {
                    if k < i as int {
                    } else {
                        assert(k == i as int);
                        if prev < curr {
                            assert(inc_prefix[k] as int == inc_prefix[k - 1] as int + 1);
                        }
                    }
                }
                assert forall |k: int| 0 <= k < i as int + 1 implies 0 <= #[trigger] dec_prefix[k] as int <= k by {
                    if k < i as int {
                    } else {
                        assert(k == i as int);
                        if prev > curr {
                            assert(dec_prefix[k] as int == dec_prefix[k - 1] as int + 1);
                        }
                    }
                }
            }
            i += 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut day: usize = 0;
        while day < n
            invariant
                n == security.len(),
                1 <= n <= 100_000,
                0 <= time <= 100_000,
                forall |k: int| 0 <= k < n ==> 0 <= #[trigger] security[k] <= 100_000,
                inc_prefix.len() == n,
                dec_prefix.len() == n,
                forall |k: int| 0 <= k < n as int ==> #[trigger] inc_prefix[k] as int == Self::inc_bad_prefix(security@, k),
                forall |k: int| 0 <= k < n as int ==> #[trigger] dec_prefix[k] as int == Self::dec_bad_prefix(security@, k),
                0 <= day <= n,
                forall |idx: int| 0 <= idx < result@.len() ==>
                    0 <= result@[idx]
                    && result@[idx] < day as i32
                    && Self::good_day(security@, time as int, result@[idx] as int),
                forall |idx: int|
                    0 <= idx < day as int
                    && (time as int) <= idx
                    && idx + (time as int) < (n as int)
                    && inc_prefix[idx] == inc_prefix[idx - (time as int)]
                    && dec_prefix[idx + (time as int)] == dec_prefix[idx]
                    ==> #[trigger] result@.contains(idx as i32),
                forall |a: int, b: int| 0 <= a < b < result@.len() ==> result@[a] < result@[b],
            decreases n - day,
        {
            let day_i = day as i32;
            if time <= day_i
                && day_i + time < n as i32
                && inc_prefix[day] == inc_prefix[(day_i - time) as usize]
                && dec_prefix[(day_i + time) as usize] == dec_prefix[day]
            {
                proof {
                    assert(Self::good_day(security@, time as int, day as int)) by {
                        assert forall |j: int| day as int - (time as int) <= j < day as int implies #[trigger] security[j] >= security[j + 1] by {
                            if security[j] < security[j + 1] {
                                Self::lemma_inc_bad_prefix_monotonic(security@, day as int - (time as int), j);
                                Self::lemma_inc_bad_prefix_monotonic(security@, j + 1, day as int);
                                assert(Self::inc_bad_step(security@, j) == 1);
                                assert(Self::inc_bad_prefix(security@, j + 1) == Self::inc_bad_prefix(security@, j) + Self::inc_bad_step(security@, j));
                                assert(Self::inc_bad_prefix(security@, day as int - (time as int)) <= Self::inc_bad_prefix(security@, j));
                                assert(Self::inc_bad_prefix(security@, j + 1) <= Self::inc_bad_prefix(security@, day as int));
                                assert(Self::inc_bad_prefix(security@, day as int - (time as int)) < Self::inc_bad_prefix(security@, day as int));
                                assert(inc_prefix[day as int - (time as int)] as int == Self::inc_bad_prefix(security@, day as int - (time as int)));
                                assert(inc_prefix[day as int] as int == Self::inc_bad_prefix(security@, day as int));
                                assert(false);
                            }
                        }
                        assert forall |j: int| day as int <= j < day as int + (time as int) implies #[trigger] security[j] <= security[j + 1] by {
                            if security[j] > security[j + 1] {
                                Self::lemma_dec_bad_prefix_monotonic(security@, day as int, j);
                                Self::lemma_dec_bad_prefix_monotonic(security@, j + 1, day as int + (time as int));
                                assert(Self::dec_bad_step(security@, j) == 1);
                                assert(Self::dec_bad_prefix(security@, j + 1) == Self::dec_bad_prefix(security@, j) + Self::dec_bad_step(security@, j));
                                assert(Self::dec_bad_prefix(security@, day as int) <= Self::dec_bad_prefix(security@, j));
                                assert(Self::dec_bad_prefix(security@, j + 1) <= Self::dec_bad_prefix(security@, day as int + (time as int)));
                                assert(Self::dec_bad_prefix(security@, day as int) < Self::dec_bad_prefix(security@, day as int + (time as int)));
                                assert(dec_prefix[day as int] as int == Self::dec_bad_prefix(security@, day as int));
                                assert(dec_prefix[day as int + (time as int)] as int == Self::dec_bad_prefix(security@, day as int + (time as int)));
                                assert(false);
                            }
                        }
                    }
                }
                let ghost old_result = result@;
                result.push(day_i);
                proof {
                    assert(result@ == old_result.push(day_i));
                    assert forall |x: i32| #[trigger] old_result.contains(x) implies result@.contains(x) by {
                        if old_result.contains(x) {
                            let p = choose |p: int| 0 <= p < old_result.len() && old_result[p] == x;
                            assert(0 <= p < result@.len());
                            assert(result@[p] == x);
                        }
                    }
                    assert(result@[result@.len() - 1] == day_i);
                    assert(result@.contains(day_i));
                    assert forall |idx: int| 0 <= idx < result@.len() implies
                        0 <= result@[idx]
                        && result@[idx] < day as i32 + 1
                        && Self::good_day(security@, time as int, result@[idx] as int) by {
                        if idx < old_result.len() {
                            assert(result@[idx] == old_result[idx]);
                        } else {
                            assert(idx == old_result.len());
                        }
                    }
                    assert forall |idx: int|
                        0 <= idx < day as int + 1
                        && (time as int) <= idx
                        && idx + (time as int) < (n as int)
                        && inc_prefix[idx] == inc_prefix[idx - (time as int)]
                        && dec_prefix[idx + (time as int)] == dec_prefix[idx]
                        implies #[trigger] result@.contains(idx as i32) by {
                        if idx < day as int {
                            assert(old_result.contains(idx as i32));
                            assert(result@.contains(idx as i32));
                        } else {
                            assert(idx == day as int);
                            assert(result@.contains(day_i));
                        }
                    }
                    assert forall |a: int, b: int| 0 <= a < b < result@.len() implies result@[a] < result@[b] by {
                        if b < old_result.len() {
                            assert(result@[a] == old_result[a]);
                            assert(result@[b] == old_result[b]);
                        } else {
                            assert(b == old_result.len());
                            assert(result@[b] == day_i);
                            assert(result@[a] == old_result[a]);
                            assert(old_result[a] < day_i);
                        }
                    }
                }
            }
            day += 1;
        }

        proof {
            assert forall |idx: int| 0 <= idx < security.len() && Self::good_day(security@, time as int, idx)
                implies #[trigger] result@.contains(idx as i32) by {
                if Self::inc_bad_prefix(security@, idx - (time as int)) < Self::inc_bad_prefix(security@, idx) {
                    Self::lemma_inc_bad_prefix_difference_has_bad(security@, idx - (time as int), idx);
                    let k = choose |k: int| idx - (time as int) <= k < idx && Self::inc_bad_step(security@, k) == 1;
                    assert(idx - (time as int) <= k < idx && Self::inc_bad_step(security@, k) == 1);
                    assert(security[k] < security[k + 1]);
                    assert(false);
                }
                Self::lemma_inc_bad_prefix_monotonic(security@, idx - (time as int), idx);
                assert(Self::inc_bad_prefix(security@, idx - (time as int)) == Self::inc_bad_prefix(security@, idx));
                if Self::dec_bad_prefix(security@, idx) < Self::dec_bad_prefix(security@, idx + (time as int)) {
                    Self::lemma_dec_bad_prefix_difference_has_bad(security@, idx, idx + (time as int));
                    let k = choose |k: int| idx <= k < idx + (time as int) && Self::dec_bad_step(security@, k) == 1;
                    assert(idx <= k < idx + (time as int) && Self::dec_bad_step(security@, k) == 1);
                    assert(security[k] > security[k + 1]);
                    assert(false);
                }
                Self::lemma_dec_bad_prefix_monotonic(security@, idx, idx + (time as int));
                assert(Self::dec_bad_prefix(security@, idx) == Self::dec_bad_prefix(security@, idx + (time as int)));
                assert(inc_prefix[idx] as int == Self::inc_bad_prefix(security@, idx));
                assert(inc_prefix[idx - (time as int)] as int == Self::inc_bad_prefix(security@, idx - (time as int)));
                assert(dec_prefix[idx] as int == Self::dec_bad_prefix(security@, idx));
                assert(dec_prefix[idx + (time as int)] as int == Self::dec_bad_prefix(security@, idx + (time as int)));
            }
        }

        result
    }
}

}
