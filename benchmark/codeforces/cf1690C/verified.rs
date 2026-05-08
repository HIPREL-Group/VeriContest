use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn duration(s: Seq<i64>, f: Seq<i64>, i: int) -> int
        recommends
            0 <= i < s.len(),
            s.len() == f.len(),
        decreases i,
    {
        if i <= 0 {
            f[0] as int - s[0] as int
        } else {
            let prev_finish = f[i - 1] as int;
            let start = if s[i] as int > prev_finish { s[i] as int } else { prev_finish };
            f[i] as int - start
        }
    }

    pub fn restore_durations(s: Vec<i64>, f: Vec<i64>) -> (result: Vec<i64>)
        requires
            s.len() == f.len(),
            1 <= s.len() <= 200_000,
            forall |k: int| 0 <= k < s.len() ==> 0 <= #[trigger] s[k] <= 1_000_000_000,
            forall |k: int| 0 <= k < f.len() ==> 0 <= #[trigger] f[k] <= 1_000_000_000,
            forall |k: int| 0 <= k < s.len() ==> s[k] < f[k],
            forall |k: int| 0 <= k < s.len() - 1 ==> #[trigger] s[k] < s[k + 1],
            forall |k: int| 0 <= k < f.len() - 1 ==> #[trigger] f[k] < f[k + 1],
        ensures
            result.len() == s.len(),
            forall |k: int| 0 <= k < result.len() ==> #[trigger] result[k] as int == Self::duration(s@, f@, k),
    {
        let n = s.len();
        let ghost s_spec = s@;
        let ghost f_spec = f@;
        let mut result: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;

        while i < n
            invariant
                n == s.len(),
                s.len() == f.len(),
                s@ == s_spec,
                f@ == f_spec,
                n <= 200_000,
                0 <= i <= n,
                result.len() == i,
                forall |k: int| 0 <= k < s.len() ==> 0 <= #[trigger] s_spec[k] <= 1_000_000_000,
                forall |k: int| 0 <= k < f.len() ==> 0 <= #[trigger] f_spec[k] <= 1_000_000_000,
                forall |k: int| 0 <= k < s.len() ==> s_spec[k] < f_spec[k],
                forall |k: int| 0 <= k < s.len() - 1 ==> #[trigger] s_spec[k] < s_spec[k + 1],
                forall |k: int| 0 <= k < f.len() - 1 ==> #[trigger] f_spec[k] < f_spec[k + 1],
                forall |k: int| 0 <= k < i ==> #[trigger] result[k] as int == Self::duration(s_spec, f_spec, k),
            decreases n - i,
        {
            let start = if i == 0 || s[i] > f[i - 1] { s[i] } else { f[i - 1] };
            let dur = f[i] - start;

            proof {
                if i == 0 {
                    assert(start as int == s_spec[0] as int);
                    assert(dur as int == f_spec[0] as int - s_spec[0] as int);
                    assert(dur as int == Self::duration(s_spec, f_spec, 0));
                } else {
                    let prev_finish = f_spec[i as int - 1] as int;
                    let spec_start = if s_spec[i as int] as int > prev_finish { s_spec[i as int] as int } else { prev_finish };
                    assert(Self::duration(s_spec, f_spec, i as int) == f_spec[i as int] as int - spec_start);
                    assert(start as int == spec_start);
                    assert(dur as int == Self::duration(s_spec, f_spec, i as int));
                }
            }

            result.push(dur);

            proof {
                assert(result[i as int] == dur);
                assert forall |k: int| 0 <= k < i + 1 implies #[trigger] result[k] as int == Self::duration(s_spec, f_spec, k) by {
                    if k < i as int {
                    } else {
                        assert(k == i as int);
                        assert(result[k] == dur);
                    }
                };
            }

            i = i + 1;
        }

        result
    }
}

}
