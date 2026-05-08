use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn dup_prefix_capped(s: Seq<i32>, end: int, n: int) -> Seq<i32>
        decreases end,
    {
        if end <= 0 {
            Seq::<i32>::empty()
        } else {
            let prev = Self::dup_prefix_capped(s, end - 1, n);
            if prev.len() >= n {
                prev
            } else if s[end - 1] == 0 {
                if prev.len() + 2 <= n {
                    prev + seq![0, 0]
                } else {
                    prev + seq![0]
                }
            } else {
                prev + seq![s[end - 1]]
            }
        }
    }

    pub open spec fn duplicate_zeros_spec(s: Seq<i32>) -> Seq<i32> {
        Self::dup_prefix_capped(s, s.len() as int, s.len() as int)
    }

    proof fn dup_prefix_capped_len_upper(s: Seq<i32>, end: int, n: int)
        requires
            0 <= n,
            0 <= end <= s.len(),
        ensures
            Self::dup_prefix_capped(s, end, n).len() <= n,
        decreases end,
    {
        if end > 0 {
            Self::dup_prefix_capped_len_upper(s, end - 1, n);
            let prev = Self::dup_prefix_capped(s, end - 1, n);
            if prev.len() >= n {
                assert(Self::dup_prefix_capped(s, end, n) == prev);
            } else if s[end - 1] == 0 {
                if prev.len() + 2 <= n {
                    assert(Self::dup_prefix_capped(s, end, n) == prev + seq![0, 0]);
                } else {
                    assert(Self::dup_prefix_capped(s, end, n) == prev + seq![0]);
                }
            } else {
                assert(Self::dup_prefix_capped(s, end, n) == prev + seq![s[end - 1]]);
            }
        }
    }

    proof fn dup_prefix_capped_len_lower(s: Seq<i32>, end: int, n: int)
        requires
            0 <= end <= n <= s.len(),
        ensures
            end <= Self::dup_prefix_capped(s, end, n).len(),
        decreases end,
    {
        if end > 0 {
            Self::dup_prefix_capped_len_lower(s, end - 1, n);
            let prev = Self::dup_prefix_capped(s, end - 1, n);
            if prev.len() >= n {
                assert(end <= prev.len()) by (nonlinear_arith)
                    requires end <= n, prev.len() >= n;
            } else if s[end - 1] == 0 {
                if prev.len() + 2 <= n {
                    assert(Self::dup_prefix_capped(s, end, n) == prev + seq![0, 0]);
                    assert(end <= (prev + seq![0, 0]).len()) by (nonlinear_arith)
                        requires end - 1 <= prev.len();
                } else {
                    assert(Self::dup_prefix_capped(s, end, n) == prev + seq![0]);
                    assert(end <= (prev + seq![0]).len()) by (nonlinear_arith)
                        requires end - 1 <= prev.len();
                }
            } else {
                assert(Self::dup_prefix_capped(s, end, n) == prev + seq![s[end - 1]]);
                assert(end <= (prev + seq![s[end - 1]]).len()) by (nonlinear_arith)
                    requires end - 1 <= prev.len();
            }
        }
    }

    pub fn duplicate_zeros(arr: &mut Vec<i32>)
        requires
            1 <= old(arr).len() <= 10_000,
            forall |i: int| 0 <= i < old(arr).len() ==> 0 <= #[trigger] old(arr)[i] <= 9,
        ensures
            arr.len() == old(arr).len(),
            arr@ == Self::duplicate_zeros_spec(old(arr)@),
    {
        let n = arr.len();
        let src = arr.clone();

        proof {
            assert(src@ =~= old(arr)@);
        }

        let mut tmp: Vec<i32> = Vec::new();
        let mut read: usize = 0;

        while read < n
            invariant
                1 <= old(arr).len() <= 10_000,
                forall |i: int| 0 <= i < old(arr).len() ==> 0 <= #[trigger] old(arr)[i] <= 9,
                n == arr.len(),
                n == old(arr).len(),
                src@ == old(arr)@,
                0 <= read <= n,
                tmp@ == Self::dup_prefix_capped(old(arr)@, read as int, n as int),
            decreases n - read,
        {
            let ghost prev = tmp@;
            let ghost prev_len = prev.len();
            let v = src[read];

            if tmp.len() < n {
                tmp.push(v);
            }
            if v == 0 && tmp.len() < n {
                tmp.push(0);
            }

            proof {
                assert(v == old(arr)[read as int]);

                if prev_len >= n as int {
                    assert(tmp@ == prev);
                    assert(Self::dup_prefix_capped(old(arr)@, read as int + 1, n as int) == prev);
                } else {
                    assert(prev_len < n as int);

                    if v != 0 {
                        assert(tmp@ == prev + seq![v]);
                        assert(Self::dup_prefix_capped(old(arr)@, read as int + 1, n as int) == prev + seq![v]);
                    } else {
                        if prev_len + 2 <= n as int {
                            assert(tmp@ == prev + seq![0, 0]);
                            assert(Self::dup_prefix_capped(old(arr)@, read as int + 1, n as int) == prev + seq![0, 0]);
                        } else {
                            assert(prev_len + 1 == n as int) by (nonlinear_arith)
                                requires prev_len < n as int, prev_len + 2 > n as int;
                            assert(tmp@ == prev + seq![0]);
                            assert(Self::dup_prefix_capped(old(arr)@, read as int + 1, n as int) == prev + seq![0]);
                        }
                    }
                }
            }

            read = read + 1;
        }

        proof {
            assert(read == n);
            assert(tmp@ == Self::dup_prefix_capped(old(arr)@, n as int, n as int));
            Self::dup_prefix_capped_len_upper(old(arr)@, n as int, n as int);
            Self::dup_prefix_capped_len_lower(old(arr)@, n as int, n as int);
            assert(tmp.len() == n);
        }

        let mut i: usize = 0;
        while i < n
            invariant
                n == arr.len(),
                n == old(arr).len(),
                tmp@ == Self::dup_prefix_capped(old(arr)@, n as int, n as int),
                tmp.len() == n,
                0 <= i <= n,
                arr@.subrange(0, i as int) == tmp@.subrange(0, i as int),
                forall |k: int| i as int <= k < n as int ==> arr[k] == old(arr)[k],
            decreases n - i,
        {
            let ghost pre = arr@;
            let val = tmp[i];
            arr[i] = val;

            proof {
                assert(arr@ =~= pre.update(i as int, val));
                assert forall |k: int| i as int + 1 <= k < n as int
                    implies arr[k] == old(arr)[k] by {
                    assert(arr[k] == pre[k]);
                };
            }

            i = i + 1;
        }

        proof {
            assert(i == n);
            assert(arr@ == arr@.subrange(0, n as int));
            assert(arr@.subrange(0, n as int) == tmp@.subrange(0, n as int));
            assert(tmp@ == tmp@.subrange(0, n as int));
            assert(arr@ == tmp@);
            assert(arr@ == Self::duplicate_zeros_spec(old(arr)@));
        }
    }
}

}
