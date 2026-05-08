use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn common_divisor(cnt: Seq<i32>, d: int) -> bool
        recommends
            cnt.len() == 30,
    {
        &&& 1 <= d
        &&& forall|b: int| 0 <= b < 30 ==> #[trigger] ((cnt[b] as int) % d) == 0
    }

    pub open spec fn valid_answer(n: int, cnt: Seq<i32>, ans: Seq<i32>) -> bool
        recommends
            cnt.len() == 30,
            n >= 1,
    {
        &&& forall|idx: int| 0 <= idx < ans.len() ==> 1 <= ans[idx] as int <= n && Self::common_divisor(cnt, ans[idx] as int)
        &&& forall|d: int| 1 <= d <= n && Self::common_divisor(cnt, d) ==> exists|idx: int| 0 <= idx < ans.len() && ans[idx] as int == d
    }

    pub fn valid_k_values(n: usize, cnt: Vec<i32>) -> (ans: Vec<i32>)
        requires
            1 <= n <= 200_000,
            cnt.len() == 30,
            forall|i: int| 0 <= i < 30 ==> 0 <= #[trigger] cnt[i] <= n,
        ensures
            Self::valid_answer(n as int, cnt@, ans@),
    {
        let mut ans: Vec<i32> = Vec::new();
        let mut k: usize = 1;

        while k <= n
            invariant
                cnt.len() == 30,
                1 <= n <= 200_000,
                1 <= k <= n + 1,
                forall|i: int| 0 <= i < 30 ==> 0 <= #[trigger] cnt[i] <= n,
                forall|idx: int| 0 <= idx < ans.len() ==> 1 <= (ans[idx] as int) && (ans[idx] as int) < (k as int) && Self::common_divisor(cnt@, ans[idx] as int),
                forall|d: int| 1 <= d < k as int && #[trigger] Self::common_divisor(cnt@, d)
                    ==> exists|idx: int| 0 <= idx < ans.len() && ans[idx] as int == d,
            decreases
                n + 1 - k,
        {
            let k_i32: i32 = k as i32;
            let mut b: usize = 0;
            let mut bad_idx: i32 = -1;
            let ghost ans_before = ans@;

            while b < 30
                invariant
                    cnt.len() == 30,
                    1 <= k <= n,
                    0 <= b <= 30,
                    1 <= k_i32,
                    k_i32 as int == k as int,
                    forall|i: int| 0 <= i < 30 ==> 0 <= #[trigger] cnt[i] <= n,
                    bad_idx == -1 ==> forall|j: int| 0 <= j < b as int ==> #[trigger] ((cnt@[j] as int) % (k as int)) == 0,
                    bad_idx != -1 ==> 0 <= bad_idx < b as int && (cnt@[bad_idx as int] as int) % (k as int) != 0,
                decreases
                    30 - b,
            {
                if bad_idx == -1 && cnt[b] % k_i32 != 0 {
                    bad_idx = b as i32;
                }
                b = b + 1;
            }

            if bad_idx == -1 {
                proof {
                    assert forall|j: int| 0 <= j < 30 implies #[trigger] ((cnt@[j] as int) % (k as int)) == 0 by {
                        assert(0 <= j < b as int);
                    }
                    assert(Self::common_divisor(cnt@, k as int));
                }
                ans.push(k as i32);
                proof {
                    assert(ans@ == ans_before.push(k as i32));
                }
            } else {
                proof {
                    assert(0 <= bad_idx < 30);
                    assert((cnt@[bad_idx as int] as int) % (k as int) != 0);
                    assert(!Self::common_divisor(cnt@, k as int));
                    assert(ans@ == ans_before);
                }
            }

            proof {
                assert forall|d: int| 1 <= d < (k as int + 1) && #[trigger] Self::common_divisor(cnt@, d)
                    implies exists|idx: int| 0 <= idx < ans@.len() && ans@[idx] as int == d by {
                    if d < k as int {
                        let idx_w = choose|idx: int| 0 <= idx < ans_before.len() && ans_before[idx] as int == d;
                        assert(0 <= idx_w < ans_before.len());
                        assert(ans_before[idx_w] as int == d);
                        if bad_idx == -1 {
                            assert(ans@ == ans_before.push(k as i32));
                            assert(ans@[idx_w] == ans_before[idx_w]);
                            assert(0 <= idx_w < ans@.len());
                        } else {
                            assert(ans@ == ans_before);
                            assert(0 <= idx_w < ans@.len());
                        }
                        assert(ans@[idx_w] as int == d);
                    } else {
                        assert(d == k as int);
                        if bad_idx == -1 {
                            let idx_new = ans@.len() - 1;
                            assert(ans@.len() > 0);
                            assert(0 <= idx_new < ans@.len());
                            assert(ans@[idx_new] as int == k as int);
                            assert(ans@[idx_new] as int == d);
                        } else {
                            assert(!Self::common_divisor(cnt@, k as int));
                            assert(false);
                        }
                    }
                }
            }

            k = k + 1;
        }

        proof {
            assert(forall|idx: int| 0 <= idx < ans@.len() ==> 1 <= ans@[idx] as int <= n as int && Self::common_divisor(cnt@, ans@[idx] as int));
            assert forall|d: int| 1 <= d <= n as int && Self::common_divisor(cnt@, d)
                implies exists|idx: int| 0 <= idx < ans@.len() && ans@[idx] as int == d by {
                assert(1 <= d < k as int);
            }
            assert(Self::valid_answer(n as int, cnt@, ans@));
        }

        ans
    }
}

}
