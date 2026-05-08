use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_sum(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::seq_sum(s, end - 1) + s[end - 1] as int
        }
    }

    proof fn seq_sum_prefix_same(s: Seq<i32>, x: i32, end: int)
        requires
            0 <= end <= s.len(),
        ensures
            Self::seq_sum(s.push(x), end) == Self::seq_sum(s, end),
        decreases end,
    {
        if end > 0 {
            Self::seq_sum_prefix_same(s, x, end - 1);
            assert(s.push(x)[end - 1] == s[end - 1]);
        }
    }

    proof fn seq_sum_push(s: Seq<i32>, x: i32)
        ensures
            Self::seq_sum(s.push(x), s.len() as int + 1) == Self::seq_sum(s, s.len() as int) + x as int,
    {
        Self::seq_sum_prefix_same(s, x, s.len() as int);
        assert(s.push(x)[s.len() as int] == x);
        assert(Self::seq_sum(s.push(x), s.len() as int) == Self::seq_sum(s, s.len() as int));
    }

    pub fn sum_zero(n: i32) -> (result: Vec<i32>)
        requires
            1 <= n <= 1000,
        ensures
            result@.len() == n as int,
            Self::seq_sum(result@, result@.len() as int) == 0,
            forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] != result@[j],
    {
        let mut ans: Vec<i32> = Vec::new();
        let half = n / 2;
        let mut i: i32 = 1;
        while i <= half
            invariant
                1 <= n <= 1000,
                half == n / 2,
                1 <= i <= half + 1,
                ans@.len() == 2 * ((i - 1) as int),
                Self::seq_sum(ans@, ans@.len() as int) == 0,
                forall|k: int| 1 <= k < i ==> #[trigger] ans@[2 * (k - 1)] == k as i32,
                forall|k: int| 1 <= k < i ==> #[trigger] ans@[2 * (k - 1) + 1] == 0i32 - k as i32,
            decreases (half - i + 1) as int,
        {
            let i0 = i;
            proof {
                assert(i0 >= 1);
                assert(i0 <= half);
                assert(2 * ((i0 - 1) as int) == ans@.len());
            }

            let ghost s0 = ans@;
            ans.push(i0);
            proof {
                Self::seq_sum_push(s0, i0);
                assert(ans@ == s0.push(i0));
                assert(Self::seq_sum(ans@, ans@.len() as int) == Self::seq_sum(s0, s0.len() as int) + i0 as int);
            }

            let ghost s1 = ans@;
            let neg_i0: i32 = -i0;
            ans.push(neg_i0);
            proof {
                Self::seq_sum_push(s1, neg_i0);
                assert(ans@ == s1.push(neg_i0));
                assert(Self::seq_sum(ans@, ans@.len() as int) == Self::seq_sum(s1, s1.len() as int) + neg_i0 as int);
                assert(Self::seq_sum(s1, s1.len() as int) == Self::seq_sum(s0, s0.len() as int) + i0 as int);
                assert(Self::seq_sum(ans@, ans@.len() as int) == Self::seq_sum(s0, s0.len() as int));
            }

            i = i + 1;

            proof {
                assert forall|k: int| 1 <= k < i implies #[trigger] ans@[2 * (k - 1)] == k as i32 by {
                    if k < i0 {
                        assert(ans@[2 * (k - 1)] == s0[2 * (k - 1)]);
                        assert(s0[2 * (k - 1)] == k as i32);
                    } else {
                        assert(k == i0);
                        assert(ans@[2 * (k - 1)] == k as i32);
                    }
                }
                assert forall|k: int| 1 <= k < i implies #[trigger] ans@[2 * (k - 1) + 1] == 0i32 - k as i32 by {
                    if k < i0 {
                        assert(ans@[2 * (k - 1) + 1] == s0[2 * (k - 1) + 1]);
                        assert(s0[2 * (k - 1) + 1] == 0i32 - k as i32);
                    } else {
                        assert(k == i0);
                        assert(ans@[2 * (k - 1) + 1] == 0i32 - k as i32);
                    }
                }
            }
        }
        if n % 2 == 1 {
            let ghost s2 = ans@;
            ans.push(0);
            proof {
                Self::seq_sum_push(s2, 0);
                assert(ans@ == s2.push(0));
                assert(Self::seq_sum(ans@, ans@.len() as int) == Self::seq_sum(s2, s2.len() as int));
            }
        }
        proof {
            if n % 2 == 0 {
                assert(n as int == 2 * (half as int));
                assert(ans@.len() == n as int);
            } else {
                assert(n as int == 2 * (half as int) + 1);
                assert(ans@.len() == n as int);
            }

            assert forall|a: int, b: int| 0 <= a < b < ans@.len() implies ans@[a] != ans@[b] by {
                if n % 2 == 1 && b == ans@.len() - 1 {
                    assert(ans@[b] == 0);
                    let t = (a / 2) + 1;
                    assert(1 <= t <= half as int);
                    if a % 2 == 0 {
                        assert(a == 2 * (t - 1));
                        assert(ans@[a] == t as i32);
                    } else {
                        assert(a == 2 * (t - 1) + 1);
                        assert(ans@[a] == 0i32 - t as i32);
                    }
                } else {
                    let ta = (a / 2) + 1;
                    let tb = (b / 2) + 1;
                    assert(1 <= ta <= half as int);
                    assert(1 <= tb <= half as int);
                    if a % 2 == 0 {
                        assert(a == 2 * (ta - 1));
                        assert(ans@[a] == ta as i32);
                    } else {
                        assert(a == 2 * (ta - 1) + 1);
                        assert(ans@[a] == 0i32 - ta as i32);
                    }
                    if b % 2 == 0 {
                        assert(b == 2 * (tb - 1));
                        assert(ans@[b] == tb as i32);
                    } else {
                        assert(b == 2 * (tb - 1) + 1);
                        assert(ans@[b] == 0i32 - tb as i32);
                    }
                    if a % 2 == b % 2 {
                        assert(ta != tb);
                    }
                }
            }
        }
        ans
    }
}

}
