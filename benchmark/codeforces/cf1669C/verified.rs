use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn can_make_same_parity_spec(s: Seq<i64>) -> bool {
    (forall|i: int|
        0 <= i < s.len() && i % 2 == 0
            ==> ((#[trigger] s[i] as int) % 2 == (s[0] as int) % 2))
    &&
    (s.len() < 2 || forall|i: int|
        0 <= i < s.len() && i % 2 == 1
            ==> ((#[trigger] s[i] as int) % 2 == (s[1] as int) % 2))
}

impl Solution {
    pub fn can_make_same_parity(a: Vec<i64>) -> (res: bool)
        requires
            1 <= a.len() <= 50,
            forall|k: int| 0 <= k < a.len() as int ==> 1 <= #[trigger] a[k] as int <= 1000,
        ensures
            res == can_make_same_parity_spec(a@),
    {
        let n = a.len();
        let mut i: usize = 0;
        while i < n
            invariant
                n == a.len(),
                1 <= n <= 50,
                (i as int) % 2 == 0,
                0 <= i <= n + 1,
                i <= 52,
                forall|k: int| 0 <= k < a.len() as int ==> 1 <= #[trigger] a[k] as int <= 1000,
                forall|k: int| 0 <= k < i as int && k < n as int && k % 2 == 0
                    ==> (#[trigger] a@[k] as int) % 2 == (a@[0] as int) % 2,
            decreases (n + 2 - i),
        {
            if a[i] % 2 != a[0] % 2 {
                proof {
                    let wi = i as int;
                    assert(0 <= wi && wi < a@.len());
                    assert(wi % 2 == 0);
                    assert((a@[wi] as int) % 2 != (a@[0] as int) % 2);
                }
                return false;
            }
            proof {
                assert((a@[i as int] as int) % 2 == (a@[0] as int) % 2);
            }
            i = i + 2;
        }

        if n >= 2 {
            let mut j: usize = 1;
            while j < n
                invariant
                    n == a.len(),
                    2 <= n <= 50,
                    (j as int) % 2 == 1,
                    1 <= j <= n + 1,
                    j <= 52,
                    forall|k: int| 0 <= k < a.len() as int ==> 1 <= #[trigger] a[k] as int <= 1000,
                    forall|k: int| 0 <= k < j as int && k < n as int && k % 2 == 1
                        ==> (#[trigger] a@[k] as int) % 2 == (a@[1] as int) % 2,
                    forall|k: int| 0 <= k < n as int && k % 2 == 0
                        ==> (#[trigger] a@[k] as int) % 2 == (a@[0] as int) % 2,
                decreases (n + 2 - j),
            {
                if a[j] % 2 != a[1] % 2 {
                    proof {
                        let wj = j as int;
                        assert(0 <= wj && wj < a@.len());
                        assert(wj % 2 == 1);
                        assert((a@[wj] as int) % 2 != (a@[1] as int) % 2);
                    }
                    return false;
                }
                proof {
                    assert((a@[j as int] as int) % 2 == (a@[1] as int) % 2);
                }
                j = j + 2;
            }
        }

        proof {
            assert forall|x: int|
                0 <= x < a@.len() && x % 2 == 0
                    implies ((#[trigger] a@[x] as int) % 2 == (a@[0] as int) % 2) by {
            };
            if n >= 2 {
                assert forall|x: int|
                    0 <= x < a@.len() && x % 2 == 1
                        implies ((#[trigger] a@[x] as int) % 2 == (a@[1] as int) % 2) by {
                };
            }
        }

        true
    }
}

}