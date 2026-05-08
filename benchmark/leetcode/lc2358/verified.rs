use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn tri(k: int) -> int
        decreases k,
    {
        if k <= 0 { 0 } else { Self::tri(k - 1) + k }
    }

    proof fn lemma_tri_step(k: int)
        requires
            k >= 0,
        ensures
            Self::tri(k + 1) == Self::tri(k) + (k + 1),
    {
        assert(k + 1 > 0);
        assert(Self::tri(k + 1) == Self::tri(k) + (k + 1));
    }

    pub fn maximum_groups(grades: Vec<i32>) -> (ans: i32)
        requires
            1 <= grades.len() <= 100000,
            forall |i: int| 0 <= i < grades.len() ==> 1 <= #[trigger] grades[i] <= 100000,
        ensures
            0 <= ans,
            Self::tri(ans as int) <= grades.len() as int,
            Self::tri(ans as int + 1) > grades.len() as int,
    {
        let n = grades.len() as i32;
        let mut k: i32 = 0;
        let mut used: i32 = 0;

        while used + (k + 1) <= n
            invariant
                1 <= n <= 100000,
                0 <= k <= n,
                used as int == Self::tri(k as int),
                0 <= used,
                used <= n,
            decreases n - k,
        {
            let ghost old_k: int = k as int;
            let ghost old_used: int = used as int;
            proof {
                assert(used + (k + 1) <= n);
                assert(used + (k + 1) <= 100000);
                assert(0 <= old_used);
                assert(old_used + (old_k + 1) <= n as int);
                assert(old_k + 1 <= n as int);
            }
            k = k + 1;
            used = used + k;
            proof {
                assert(old_used == Self::tri(old_k));
                Self::lemma_tri_step(old_k);
                assert(k as int == old_k + 1);
                assert(used as int == old_used + (old_k + 1));
                assert(used as int == Self::tri(k as int));
                assert(k as int <= n as int);
            }
        }

        proof {
            assert(used as int == Self::tri(k as int));
            assert(Self::tri(k as int) <= n as int);
            assert(!(used + (k + 1) <= n));
            assert(used as int + (k as int + 1) > n as int);
            Self::lemma_tri_step(k as int);
            assert(Self::tri(k as int + 1) > n as int);
        }

        k
    }
}

}
