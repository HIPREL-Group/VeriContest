use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn left_run_len_from(s: Seq<i64>, i: int) -> int
    decreases s.len() - i
{
    if i >= s.len() || s[i] != s[0] {
        i
    } else {
        left_run_len_from(s, i + 1)
    }
}

pub open spec fn left_run_len(s: Seq<i64>) -> int {
    left_run_len_from(s, 0)
}

pub open spec fn right_run_len_from(s: Seq<i64>, k: int) -> int
    decreases s.len() - k
{
    if k >= s.len() || s[s.len() - 1 - k] != s[s.len() - 1] {
        k
    } else {
        right_run_len_from(s, k + 1)
    }
}

pub open spec fn right_run_len(s: Seq<i64>) -> int {
    right_run_len_from(s, 0)
}

pub open spec fn min_int(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn expected_min_cost(s: Seq<i64>) -> int {
    let n = s.len() as int;
    let left = left_run_len(s);
    let right = right_run_len(s);
    if s[0] == s[n - 1] {
        let keep = if left + right <= n { left + right } else { n };
        n - keep
    } else {
        min_int(n - left, n - right)
    }
}

proof fn lemma_left_step(s: Seq<i64>, i: int)
    requires
        0 <= i < s.len(),
        s[i] == s[0],
    ensures
        left_run_len_from(s, i) == left_run_len_from(s, i + 1),
{
}

proof fn lemma_right_step(s: Seq<i64>, k: int)
    requires
        0 <= k < s.len(),
        s[s.len() - 1 - k] == s[s.len() - 1],
    ensures
        right_run_len_from(s, k) == right_run_len_from(s, k + 1),
{
}

pub struct Solution;

impl Solution {
    pub fn min_cost_make_equal(a: Vec<i64>) -> (res: i64)
        requires
            1 <= a.len() <= 200000,
        ensures
            res >= 0,
            res as int == expected_min_cost(a@),
    {
        let n: usize = a.len();

        let mut left: usize = 0;
        while left < n && a[left] == a[0]
            invariant
                0 <= left <= n,
                a.len() == n,
                left_run_len_from(a@, left as int) == left_run_len(a@),
            decreases n - left,
        {
            proof {
                lemma_left_step(a@, left as int);
            }
            left += 1;
        }
        assert(left_run_len_from(a@, left as int) == left_run_len(a@));
        if left < n {
            assert(a[left as int] != a[0]);
        }
        assert(left_run_len_from(a@, left as int) == left as int);
        assert(left as int == left_run_len(a@));

        let mut right: usize = 0;
        while right < n && a[n - 1 - right] == a[n - 1]
            invariant
                0 <= right <= n,
                a.len() == n,
                right_run_len_from(a@, right as int) == right_run_len(a@),
            decreases n - right,
        {
            proof {
                lemma_right_step(a@, right as int);
            }
            right += 1;
        }
        assert(right_run_len_from(a@, right as int) == right_run_len(a@));
        if right < n {
            assert(a[(n - 1 - right) as int] != a[(n - 1) as int]);
        }
        assert(right_run_len_from(a@, right as int) == right as int);
        assert(right as int == right_run_len(a@));

        let mut ans: usize = if n - left <= n - right { n - left } else { n - right };
        if a[0] == a[n - 1] {
            let keep = if left + right <= n { left + right } else { n };
            ans = n - keep;
        }

        let out = ans as i64;
        assert(out >= 0);

        proof {
            let ni = n as int;
            let li = left as int;
            let ri = right as int;
            assert(li == left_run_len(a@));
            assert(ri == right_run_len(a@));
            if a@[0] == a@[ni - 1] {
                let keep = if li + ri <= ni { li + ri } else { ni };
                assert(expected_min_cost(a@) == ni - keep);
                assert(ans as int == ni - keep);
            } else {
                assert(expected_min_cost(a@) == min_int(ni - li, ni - ri));
                assert(ans as int == min_int(ni - li, ni - ri));
            }
        }

        out
    }
}

}
