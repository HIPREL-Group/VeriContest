use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn prefix_sum_to(s: Seq<i64>, end: int) -> int
    recommends
        0 <= end <= s.len(),
    decreases
        end,
{
    if end <= 0 {
        0
    } else {
        prefix_sum_to(s, end - 1) + s[end - 1] as int
    }
}

pub open spec fn total_sum(s: Seq<i64>) -> int {
    prefix_sum_to(s, s.len() as int)
}

pub open spec fn count_gt_prefix(s: Seq<i64>, avg: int, end: int) -> int
    recommends
        0 <= end <= s.len(),
    decreases
        end,
{
    if end <= 0 {
        0
    } else {
        count_gt_prefix(s, avg, end - 1) + if s[end - 1] as int > avg {
            1int
        } else {
            0int
        }
    }
}

pub open spec fn friends_candies_answer(s: Seq<i64>) -> int {
    let n = s.len() as int;
    let sum = total_sum(s);
    if n == 0 {
        0
    } else if (sum % n) != 0 {
        -1
    } else {
        let avg = sum / n;
        count_gt_prefix(s, avg, n)
    }
}

proof fn lemma_prefix_sum_to_total(s: Seq<i64>)
    ensures
        prefix_sum_to(s, s.len() as int) == total_sum(s),
{}

proof fn lemma_prefix_sum_step(s: Seq<i64>, end: int)
    requires
        0 < end <= s.len(),
    ensures
        prefix_sum_to(s, end) == prefix_sum_to(s, end - 1) + s[end - 1] as int,
{}

proof fn lemma_i64_div_mod_nonneg(a: i64, b: i64)
    requires
        a >= 0,
        b > 0,
    ensures
        (a / b) as int == (a as int) / (b as int),
        (a % b) as int == (a as int) % (b as int),
{
}

proof fn lemma_ni_eq_len(n: usize, ni: i64)
    requires
        n <= 200_000,
        ni == (n as i64),
    ensures
        (ni as int) == (n as int),
{
}

proof fn lemma_prefix_sum_bounded(s: Seq<i64>, end: int)
    requires
        0 <= end <= s.len(),
        forall |k: int| 0 <= k < s.len() ==> 0 <= #[trigger] s[k] <= 10_000,
    ensures
        prefix_sum_to(s, end) <= end * 10_000,
    decreases
        end,
{
    if end > 0 {
        lemma_prefix_sum_bounded(s, end - 1);
        assert(prefix_sum_to(s, end) == prefix_sum_to(s, end - 1) + s[end - 1] as int);
        assert(s[end - 1] as int <= 10_000);
        assert(prefix_sum_to(s, end - 1) <= (end - 1) * 10_000);
    }
}

proof fn lemma_count_gt_step(s: Seq<i64>, avg: int, end: int)
    requires
        0 < end <= s.len(),
    ensures
        count_gt_prefix(s, avg, end) == count_gt_prefix(s, avg, end - 1)
            + if s[end - 1] as int > avg {
                1int
            } else {
                0int
            },
{}

proof fn lemma_friends_when_indivisible(s: Seq<i64>)
    requires
        s.len() >= 1,
        (total_sum(s) % (s.len() as int)) != 0,
    ensures
        friends_candies_answer(s) == -1,
{}

proof fn lemma_friends_when_divisible(s: Seq<i64>)
    requires
        s.len() >= 1,
        (total_sum(s) % (s.len() as int)) == 0,
    ensures
        friends_candies_answer(s) == count_gt_prefix(s, total_sum(s) / (s.len() as int), s.len() as int),
{}

impl Solution {
    pub fn min_friends_for_equal_candies(a: Vec<i64>) -> (result: i32)
        requires
            1 <= a.len() <= 200_000,
            forall |k: int| 0 <= k < a.len() ==> 0 <= #[trigger] a[k] <= 10_000,
        ensures
            result as int == friends_candies_answer(a@),
    {
        let n = a.len();
        let ni = n as i64;
        proof {
            lemma_ni_eq_len(n, ni);
        }
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == a.len(),
                1 <= n <= 200_000,
                forall |k: int| 0 <= k < a.len() ==> 0 <= #[trigger] a[k] <= 10_000,
                sum as int == prefix_sum_to(a@, i as int),
                sum >= 0,
                sum as int <= (i as int) * 10_000,
            decreases n - i,
        {
            proof {
                lemma_prefix_sum_step(a@, (i + 1) as int);
                assert((sum as int) + (a@[i as int] as int) <= (i as int) * 10_000 + 10_000);
                assert((i as int) * 10_000 + 10_000 == ((i + 1) as int) * 10_000);
                assert((i as int) + 1 == (i + 1) as int);
                assert(prefix_sum_to(a@, i as int) <= (i as int) * 10_000) by {
                    lemma_prefix_sum_bounded(a@, i as int);
                }
                assert(a@[i as int] as int <= 10_000);
                assert((sum as int) + (a@[i as int] as int) <= 2_000_000_000);
                assert(2_000_000_000 < 0x7fffffffffffffff);
            }
            sum = sum + a[i];
            i = i + 1;
            proof {
                assert(sum as int == prefix_sum_to(a@, i as int));
            }
        }
        proof {
            assert(i == n);
            assert(sum as int == prefix_sum_to(a@, n as int));
            lemma_prefix_sum_to_total(a@);
            assert(sum as int == total_sum(a@));
            lemma_i64_div_mod_nonneg(sum, ni);
            assert(ni > 0);
            assert(sum >= 0);
        }
        if sum % ni != 0 {
            proof {
                assert((sum % ni) as int != 0);
                assert((sum as int) % (ni as int) != 0);
                lemma_ni_eq_len(n, ni);
                assert((ni as int) == (a@.len() as int));
                assert((sum as int) % (a@.len() as int) != 0);
                lemma_friends_when_indivisible(a@);
                assert(friends_candies_answer(a@) == -1);
            }
            return -1;
        }
        let t = sum / ni;
        proof {
            assert((sum % ni) as int == 0);
            assert((sum as int) % (ni as int) == 0);
            lemma_ni_eq_len(n, ni);
            assert((ni as int) == (a@.len() as int));
            assert((sum as int) % (a@.len() as int) == 0);
            lemma_friends_when_divisible(a@);
            assert((t as int) == (sum / ni) as int);
            assert((t as int) == total_sum(a@) / (a@.len() as int));
        }
        let mut cnt: i32 = 0;
        i = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == a.len(),
                1 <= n <= 200_000,
                forall |k: int| 0 <= k < a.len() ==> 0 <= #[trigger] a[k] <= 10_000,
                sum as int == total_sum(a@),
                (sum as int) % (a@.len() as int) == 0,
                t == sum / ni,
                (t as int) == total_sum(a@) / (a@.len() as int),
                cnt as int == count_gt_prefix(a@, t as int, i as int),
                cnt >= 0,
                cnt as int <= i as int,
            decreases n - i,
        {
            proof {
                lemma_count_gt_step(a@, t as int, (i + 1) as int);
            }
            if a[i] > t {
                proof {
                    assert((cnt + 1) as int <= n as int);
                    assert((cnt + 1) as int <= 200_000);
                }
                cnt = cnt + 1;
            } else {
                proof {
                    assert(cnt as int == count_gt_prefix(a@, t as int, (i + 1) as int));
                }
            }
            proof {
                assert(cnt as int == count_gt_prefix(a@, t as int, (i + 1) as int));
            }
            i = i + 1;
            proof {
                assert(cnt as int == count_gt_prefix(a@, t as int, i as int));
            }
        }
        proof {
            assert(i == n);
            assert(cnt as int == count_gt_prefix(a@, t as int, n as int));
            assert((t as int) == total_sum(a@) / (a@.len() as int));
            assert(friends_candies_answer(a@) == cnt as int);
        }
        cnt
    }
}

}
