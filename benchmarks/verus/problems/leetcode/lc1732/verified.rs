use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn altitude_at(gain: Seq<i32>, k: int) -> int
        decreases k
    {
        if k <= 0 {
            0
        } else {
            Self::altitude_at(gain, k - 1) + gain[k - 1] as int
        }
    }

    proof fn altitude_bounds(gain: Seq<i32>, k: int)
        requires
            0 <= k <= gain.len(),
            forall|j: int| 0 <= j < gain.len() ==> -100 <= #[trigger] gain[j] <= 100,
        ensures
            -100 * k <= Self::altitude_at(gain, k) <= 100 * k,
        decreases k
    {
        if k > 0 {
            Self::altitude_bounds(gain, k - 1);
            assert(Self::altitude_at(gain, k) == Self::altitude_at(gain, k - 1) + gain[k - 1] as int);
        }
    }

    pub fn largest_altitude(gain: Vec<i32>) -> (result: i32)
        requires
            1 <= gain.len() <= 100,
            forall|i: int| 0 <= i < gain.len() ==> -100 <= #[trigger] gain[i] <= 100,
        ensures
            exists|k: int| 0 <= k <= gain.len() && result == Self::altitude_at(gain@, k),
            forall|k: int| 0 <= k <= gain.len() ==> Self::altitude_at(gain@, k) <= result,
    {
        let mut max_alt: i32 = 0;
        let mut cur: i32 = 0;
        let n = gain.len();
        let mut i: usize = 0;

        while i < n
            invariant
                0 <= i <= n,
                n == gain.len(),
                1 <= n <= 100,
                forall|j: int| 0 <= j < n ==> -100 <= #[trigger] gain[j] <= 100,
                cur as int == Self::altitude_at(gain@, i as int),
                -10000 <= cur <= 10000,
                -10000 <= max_alt <= 10000,
                exists|k: int| 0 <= k <= i && max_alt as int == Self::altitude_at(gain@, k),
                forall|k: int| 0 <= k <= i ==> #[trigger] Self::altitude_at(gain@, k) <= max_alt as int,
            decreases n - i,
        {
            proof {
                assert(Self::altitude_at(gain@, i as int + 1) == Self::altitude_at(gain@, i as int) + gain@[i as int] as int);
                Self::altitude_bounds(gain@, i as int + 1);
                assert(-10000 <= Self::altitude_at(gain@, i as int + 1) <= 10000) by (nonlinear_arith)
                    requires
                        -100 * (i as int + 1) <= Self::altitude_at(gain@, i as int + 1),
                        Self::altitude_at(gain@, i as int + 1) <= 100 * (i as int + 1),
                        i < n,
                        n <= 100;
            }
            cur = cur + gain[i];
            proof {
                assert(cur as int == Self::altitude_at(gain@, i as int + 1));
                assert forall|k: int| 0 <= k <= i as int + 1 implies Self::altitude_at(gain@, k) <= (if cur > max_alt { cur } else { max_alt }) as int by {
                    if k <= i as int {
                        assert(Self::altitude_at(gain@, k) <= max_alt as int);
                    }
                };
            }
            if cur > max_alt {
                max_alt = cur;
            }
            i += 1;
        }
        max_alt
    }
}

}
