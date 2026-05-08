use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sorted(s: Seq<i64>, n: int) -> bool {
    n <= s.len() && forall|i: int| 0 <= i < n - 1 ==> #[trigger] s[i] <= s[i + 1]
}

pub open spec fn spec_sum_upto(s: Seq<i64>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 }
    else { spec_sum_upto(s, n - 1) + s[n - 1] }
}

pub open spec fn spec_step(
    s: Seq<i64>, n: int, k: int, pos: int,
    botnum: int, prsnum: int, prev: int, first: bool,
) -> int
    decreases n - pos,
{
    if pos >= n {
        prsnum
    } else if pos > 0 && s[pos] == s[pos - 1] {
        spec_step(s, n, k, pos + 1, botnum, prsnum, prev, first)
    } else {
        let cnt = n - pos;
        let delta = if pos == 0 { s[0] as int } else { (s[pos] - s[pos - 1]) as int };
        let prs2 = if first { prsnum } else { prsnum + (pos - prev) };
        let prod = cnt * delta;
        if botnum + prod >= k {
            prs2 + (k - botnum)
        } else {
            spec_step(s, n, k, pos + 1, botnum + prod, prs2 + prod, pos, false)
        }
    }
}

pub open spec fn spec_answer(s: Seq<i64>, n: int, k: int) -> int {
    spec_step(s, n, k, 0, 0, 0, 0, true)
}

proof fn lemma_skip_equal(
    s: Seq<i64>, n: int, k: int, pos: int, j: int,
    botnum: int, prsnum: int, prev: int,
)
    requires
        0 <= pos,
        pos <= j,
        j < n,
        n == s.len(),
        forall|t: int| pos <= t <= j ==> s[t] == s[pos],
    ensures
        spec_step(s, n, k, pos + 1, botnum, prsnum, prev, false)
            == spec_step(s, n, k, j + 1, botnum, prsnum, prev, false),
    decreases j - pos,
{
    if j > pos {
        assert(s[pos + 1] == s[pos]);
        assert((pos + 1) > 0 && s[pos + 1] == s[(pos + 1) - 1]);
        lemma_skip_equal(s, n, k, pos + 1, j, botnum, prsnum, prev);
    }
}

impl Solution {
    pub fn min_lemonade_presses(n: usize, k: i64, a: Vec<i64>) -> (res: i64)
        requires
            1 <= n <= 200_000,
            n == a.len(),
            sorted(a@, n as int),
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] && a[i] <= 1_000_000_000,
            1 <= k <= 1_000_000_000,
        ensures
            res as int == spec_answer(a@, n as int, k as int),
    {
        let mut pos = 0usize;
        let mut botnum = 0i64;
        let mut prsnum = 0i64;
        let mut prev_pos = 0usize;
        let mut first = true;

        while pos < n
            invariant
                n == a.len(),
                1 <= n <= 200_000,
                pos <= n,
                sorted(a@, n as int),
                forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] && a[i] <= 1_000_000_000,
                1 <= k <= 1_000_000_000,
                pos == 0 || (pos as int) >= (n as int)
                    || a@[pos as int] != a@[(pos - 1) as int],
                first ==> (pos == 0 && botnum == 0 && prsnum == 0),
                !first ==> (prev_pos as int) < (pos as int),
                0 <= botnum,
                (botnum as int) < (k as int),
                0 <= prsnum,
                first || (prsnum as int) == (botnum as int) + (prev_pos as int),
                spec_step(a@, n as int, k as int, pos as int, botnum as int,
                    prsnum as int, prev_pos as int, first)
                    == spec_answer(a@, n as int, k as int),
            decreases n - pos,
        {
            proof {
                if pos > 0 {
                    assert(a@[pos as int] != a@[(pos as int) - 1]);
                }
            }

            let cnt = (n - pos) as i64;
            let delta = if pos == 0 {
                a[0]
            } else {
                proof {
                    let p = pos as int;
                    assert(a@[p - 1] <= a@[p]);
                }
                a[pos] - a[pos - 1]
            };

            if !first {
                proof {
                    assert((prsnum as int) == (botnum as int) + (prev_pos as int));
                    assert((botnum as int) < (k as int) && (k as int) <= 1_000_000_000);
                    assert((prev_pos as int) < (pos as int) && (pos as int) <= (n as int)
                        && (n as int) <= 200_000);
                }
                prsnum = prsnum + ((pos - prev_pos) as i64);
            }
            first = false;

            proof {
                assert((prsnum as int) == (botnum as int) + (pos as int));
                assert(1 <= cnt && (cnt as int) <= 200_000);
                assert(0 <= delta && (delta as int) <= 1_000_000_000);
                assert((cnt as int) * (delta as int) <= 200_000 * 1_000_000_000)
                    by(nonlinear_arith)
                    requires
                        1 <= cnt as int <= 200_000,
                        0 <= delta as int <= 1_000_000_000,
                ;
                assert(200_000i64 * 1_000_000_000i64 == 200_000_000_000_000i64);
                assert((botnum as int) + (cnt as int) * (delta as int) <=
                    1_000_000_000 + 200_000_000_000_000);
            }

            let prod = cnt * delta;

            if botnum + prod >= k {
                proof {
                    assert((k as int) - (botnum as int) >= 0);
                    assert((prsnum as int) + ((k as int) - (botnum as int))
                        <= (botnum as int) + (pos as int) + (k as int));
                    assert((botnum as int) + (pos as int) + (k as int)
                        <= 1_000_000_000 + 200_000 + 1_000_000_000);
                }
                prsnum = prsnum + (k - botnum);
                return prsnum;
            }

            proof {
                assert((botnum as int) + (prod as int) < (k as int));
                assert((prsnum as int) + (prod as int)
                    == (botnum as int) + (pos as int) + (prod as int));
                assert((botnum as int) + (prod as int) < 1_000_000_000);
                assert((prsnum as int) + (prod as int) < 1_000_000_000 + 200_000);
            }

            prsnum = prsnum + prod;
            botnum = botnum + prod;
            prev_pos = pos;

            let mut j = pos;
            while j + 1 < n && a[j + 1] == a[j]
                invariant
                    pos <= j,
                    j < n,
                    n == a.len(),
                    forall|t: int| (pos as int) <= t <= (j as int) ==> a@[t] == a@[pos as int],
                decreases n - j,
            {
                proof {
                    assert(a@[(j + 1) as int] == a@[j as int]);
                    assert(a@[j as int] == a@[pos as int]);
                }
                j = j + 1;
            }

            proof {
                lemma_skip_equal(a@, n as int, k as int, pos as int, j as int,
                    botnum as int, prsnum as int, prev_pos as int);
            }

            pos = j + 1;

            proof {
                assert(pos == 0 || pos >= n || a@[pos as int] != a@[(pos - 1) as int]);
                assert((prsnum as int) == (botnum as int) + (prev_pos as int));
                assert((botnum as int) < (k as int));
            }
        }

        prsnum
    }
}

}
