use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_ops_suffix(s: Seq<i64>, i: int, started: bool) -> int
    recommends
        0 <= i <= s.len(),
    decreases s.len() - i,
{
    if i >= s.len() - 1 {
        0int
    } else {
        let ai = s[i] as int;
        if ai > 0 {
            ai + spec_ops_suffix(s, i + 1, true)
        } else if started {
            1int + spec_ops_suffix(s, i + 1, true)
        } else {
            spec_ops_suffix(s, i + 1, false)
        }
    }
}

pub open spec fn spec_min_operations(s: Seq<i64>) -> int
    recommends
        s.len() >= 2,
{
    spec_ops_suffix(s, 0, false)
}

impl Solution {
    pub fn min_operations(a: Vec<i64>) -> (res: i64)
        requires
            2 <= a.len() <= 200000,
            forall|j: int| 0 <= j < a.len() as int ==> 0 <= #[trigger] a[j] as int <= 1000000000,
        ensures
            res as int == spec_min_operations(a@),
    {
        let n = a.len();
        let mut ans: i64 = 0;
        let mut started: bool = false;
        let mut i: usize = 0;
        while i + 1 < n
            invariant
                n == a.len(),
                n >= 2,
                n <= 200000,
                i < n,
                0 <= ans as int,
                ans as int <= (i as int) * 1000000001int,
                forall|j: int| 0 <= j < a.len() as int ==> 0 <= #[trigger] a[j] as int <= 1000000000,
                ans as int + spec_ops_suffix(a@, i as int, started) == spec_min_operations(a@),
            decreases n - 1 - i,
        {
            proof {
                assert(i as int <= a@.len() - 2);
            }
            let ai = a[i];
            let prev_ans = ans;
            let prev_started = started;
            if ai > 0 {
                proof {
                    assert(0 <= (i as int));
                    assert((i as int) < (a.len() as int));
                    assert(0 <= (a@[i as int] as int));
                    assert((a@[i as int] as int) <= 1000000000);
                    assert((ai as int) == (a@[i as int] as int));
                    assert((prev_ans as int) <= ((i as int) * 1000000001int));
                    assert((ai as int) <= 1000000000);
                    assert(i + 1 < n);
                    assert((i as int) <= 199999);
                    assert((prev_ans as int) + (ai as int) <= ((i as int) * 1000000001int) + 1000000000int);
                    assert((i as int) * 1000000001int + 1000000000int <= 200000int * 1000000001int);
                    assert((prev_ans as int) + (ai as int) < 9223372036854775807);
                }
                ans = ans + ai;
                started = true;
            } else if started {
                ans = ans + 1;
            }
            proof {
                assert(ai as int == a@[i as int] as int);
                if ai > 0 {
                    assert(spec_ops_suffix(a@, i as int, prev_started) == ai as int + spec_ops_suffix(a@, i as int + 1, true));
                    assert(ans as int == prev_ans as int + ai as int);
                    assert(started);
                    assert(ans as int + spec_ops_suffix(a@, i as int + 1, started) == prev_ans as int + spec_ops_suffix(a@, i as int, prev_started));
                } else if prev_started {
                    assert(spec_ops_suffix(a@, i as int, prev_started) == 1int + spec_ops_suffix(a@, i as int + 1, true));
                    assert(ans as int == prev_ans as int + 1);
                    assert(started == prev_started);
                    assert(ans as int + spec_ops_suffix(a@, i as int + 1, started) == prev_ans as int + spec_ops_suffix(a@, i as int, prev_started));
                } else {
                    assert(spec_ops_suffix(a@, i as int, prev_started) == spec_ops_suffix(a@, i as int + 1, false));
                    assert(ans as int == prev_ans as int);
                    assert(!started);
                    assert(ans as int + spec_ops_suffix(a@, i as int + 1, started) == prev_ans as int + spec_ops_suffix(a@, i as int, prev_started));
                }
                if ai > 0 {
                    assert(ans as int == prev_ans as int + ai as int);
                    assert(prev_ans as int <= (i as int) * 1000000001int);
                    assert(ai as int <= 1000000000);
                    assert(ans as int <= (i as int) * 1000000001int + 1000000000int);
                    assert(ans as int <= ((i as int) + 1int) * 1000000001int);
                } else if prev_started {
                    assert(ans as int <= prev_ans as int + 1);
                    assert(prev_ans as int <= (i as int) * 1000000001int);
                    assert(ans as int <= ((i as int) + 1int) * 1000000001int);
                } else {
                    assert(ans as int <= prev_ans as int);
                    assert(prev_ans as int <= (i as int) * 1000000001int);
                    assert(ans as int <= ((i as int) + 1int) * 1000000001int);
                }
            }
            i = i + 1;
        }
        proof {
            assert(i == n - 1);
            assert(spec_ops_suffix(a@, i as int, started) == 0);
            assert(ans as int == spec_min_operations(a@));
        }
        ans
    }
}

}
