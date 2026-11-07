use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count(s: Seq<i32>, v: i32) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            Self::count(s.drop_last(), v) + if s.last() == v { 1int } else { 0int }
        }
    }

    pub open spec fn filter_even(s: Seq<i32>, n: int) -> Seq<i32>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else if s[n - 1] % 2 == 0 {
            Self::filter_even(s, n - 1).push(s[n - 1])
        } else {
            Self::filter_even(s, n - 1)
        }
    }

    pub open spec fn filter_odd(s: Seq<i32>, n: int) -> Seq<i32>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else if s[n - 1] % 2 != 0 {
            Self::filter_odd(s, n - 1).push(s[n - 1])
        } else {
            Self::filter_odd(s, n - 1)
        }
    }

    pub open spec fn interleave(a: Seq<i32>, b: Seq<i32>, n: int) -> Seq<i32>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else {
            Self::interleave(a, b, n - 1).push(a[n - 1]).push(b[n - 1])
        }
    }

    proof fn filter_split_len(s: Seq<i32>, n: int)
        requires
            0 <= n <= s.len(),
        ensures
            Self::filter_even(s, n).len() + Self::filter_odd(s, n).len() == n,
        decreases n,
    {
        if n > 0 {
            Self::filter_split_len(s, n - 1);
        }
    }

    proof fn filter_even_values_even(s: Seq<i32>, n: int)
        requires
            0 <= n <= s.len(),
        ensures
            forall |k: int| 0 <= k < Self::filter_even(s, n).len() ==> Self::filter_even(s, n)[k] % 2 == 0,
        decreases n,
    {
        if n > 0 {
            Self::filter_even_values_even(s, n - 1);
            assert forall |k: int| 0 <= k < Self::filter_even(s, n).len() implies Self::filter_even(s, n)[k] % 2 == 0 by {
                if s[n - 1] % 2 == 0 {
                    if k < Self::filter_even(s, n - 1).len() {
                    } else {
                        assert(k == Self::filter_even(s, n - 1).len());
                        assert(Self::filter_even(s, n)[k] == s[n - 1]);
                    }
                } else {
                }
            }
        }
    }

    proof fn filter_odd_values_odd(s: Seq<i32>, n: int)
        requires
            0 <= n <= s.len(),
        ensures
            forall |k: int| 0 <= k < Self::filter_odd(s, n).len() ==> Self::filter_odd(s, n)[k] % 2 != 0,
        decreases n,
    {
        if n > 0 {
            Self::filter_odd_values_odd(s, n - 1);
            assert forall |k: int| 0 <= k < Self::filter_odd(s, n).len() implies Self::filter_odd(s, n)[k] % 2 != 0 by {
                if s[n - 1] % 2 != 0 {
                    if k < Self::filter_odd(s, n - 1).len() {
                    } else {
                        assert(k == Self::filter_odd(s, n - 1).len());
                        assert(Self::filter_odd(s, n)[k] == s[n - 1]);
                    }
                } else {
                }
            }
        }
    }

    proof fn count_filter_split(s: Seq<i32>, v: i32, n: int)
        requires
            0 <= n <= s.len(),
        ensures
            Self::count(Self::filter_even(s, n), v) + Self::count(Self::filter_odd(s, n), v)
                == Self::count(s.subrange(0, n), v),
        decreases n,
    {
        if n > 0 {
            Self::count_filter_split(s, v, n - 1);
            assert(s.subrange(0, n) =~= s.subrange(0, n - 1).push(s[n - 1]));
            assert(s.subrange(0, n).drop_last() =~= s.subrange(0, n - 1));
            assert(s.subrange(0, n).last() == s[n - 1]);
            assert(Self::count(s.subrange(0, n), v)
                == Self::count(s.subrange(0, n - 1), v) + if s[n - 1] == v { 1int } else { 0int });
            if s[n - 1] % 2 == 0 {
                assert(Self::filter_odd(s, n) == Self::filter_odd(s, n - 1));
                assert(Self::filter_even(s, n) == Self::filter_even(s, n - 1).push(s[n - 1]));
                assert(Self::filter_even(s, n).drop_last() =~= Self::filter_even(s, n - 1));
                assert(Self::filter_even(s, n).last() == s[n - 1]);
                assert(Self::count(Self::filter_even(s, n), v)
                    == Self::count(Self::filter_even(s, n - 1), v) + if s[n - 1] == v { 1int } else { 0int });
            } else {
                assert(Self::filter_even(s, n) == Self::filter_even(s, n - 1));
                assert(Self::filter_odd(s, n) == Self::filter_odd(s, n - 1).push(s[n - 1]));
                assert(Self::filter_odd(s, n).drop_last() =~= Self::filter_odd(s, n - 1));
                assert(Self::filter_odd(s, n).last() == s[n - 1]);
                assert(Self::count(Self::filter_odd(s, n), v)
                    == Self::count(Self::filter_odd(s, n - 1), v) + if s[n - 1] == v { 1int } else { 0int });
            }
        }
    }

    proof fn count_interleave(a: Seq<i32>, b: Seq<i32>, v: i32, n: int)
        requires
            0 <= n <= a.len(),
            n <= b.len(),
        ensures
            Self::count(Self::interleave(a, b, n), v)
                == Self::count(a.subrange(0, n), v) + Self::count(b.subrange(0, n), v),
        decreases n,
    {
        if n > 0 {
            Self::count_interleave(a, b, v, n - 1);
            assert(a.subrange(0, n) =~= a.subrange(0, n - 1).push(a[n - 1]));
            assert(b.subrange(0, n) =~= b.subrange(0, n - 1).push(b[n - 1]));
            assert(Self::interleave(a, b, n) == Self::interleave(a, b, n - 1).push(a[n - 1]).push(b[n - 1]));
            assert(Self::interleave(a, b, n).drop_last() =~= Self::interleave(a, b, n - 1).push(a[n - 1]));
            assert(Self::interleave(a, b, n).last() == b[n - 1]);
            assert(Self::interleave(a, b, n - 1).push(a[n - 1]).drop_last() =~= Self::interleave(a, b, n - 1));
            assert(Self::interleave(a, b, n - 1).push(a[n - 1]).last() == a[n - 1]);
            assert(a.subrange(0, n).drop_last() =~= a.subrange(0, n - 1));
            assert(a.subrange(0, n).last() == a[n - 1]);
            assert(b.subrange(0, n).drop_last() =~= b.subrange(0, n - 1));
            assert(b.subrange(0, n).last() == b[n - 1]);
            assert(Self::count(Self::interleave(a, b, n), v)
                == Self::count(Self::interleave(a, b, n - 1).push(a[n - 1]), v)
                    + if b[n - 1] == v { 1int } else { 0int });
            assert(Self::count(Self::interleave(a, b, n - 1).push(a[n - 1]), v)
                == Self::count(Self::interleave(a, b, n - 1), v)
                    + if a[n - 1] == v { 1int } else { 0int });
            assert(Self::count(a.subrange(0, n), v)
                == Self::count(a.subrange(0, n - 1), v) + if a[n - 1] == v { 1int } else { 0int });
            assert(Self::count(b.subrange(0, n), v)
                == Self::count(b.subrange(0, n - 1), v) + if b[n - 1] == v { 1int } else { 0int });
        }
    }

    pub fn sort_array_by_parity_ii(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 20000,
            nums.len() % 2 == 0,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
            Self::filter_even(nums@, nums.len() as int).len() == nums.len() as int / 2,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < result.len() && i % 2 == 0 ==> result[i] % 2 == 0,
            forall |i: int| 0 <= i < result.len() && i % 2 != 0 ==> result[i] % 2 != 0,
            forall |v: i32| Self::count(result@, v) == Self::count(nums@, v),
    {
        let n = nums.len();
        let mut evens: Vec<i32> = Vec::new();
        let mut odds: Vec<i32> = Vec::new();
        let mut i: usize = 0;

        while i < n
            invariant
                n == nums.len(),
                2 <= n <= 20000,
                n % 2 == 0,
                0 <= i <= n,
                forall |k: int| 0 <= k < n as int ==> 0 <= #[trigger] nums[k] <= 1000,
                evens@ == Self::filter_even(nums@, i as int),
                odds@ == Self::filter_odd(nums@, i as int),
                forall |k: int| 0 <= k < evens.len() ==> evens[k] % 2 == 0,
                forall |k: int| 0 <= k < odds.len() ==> odds[k] % 2 != 0,
            decreases n - i,
        {
            if nums[i] % 2 == 0 {
                evens.push(nums[i]);
            } else {
                odds.push(nums[i]);
            }
            i = i + 1;
        }

        proof {
            Self::filter_split_len(nums@, n as int);
            Self::filter_even_values_even(nums@, n as int);
            Self::filter_odd_values_odd(nums@, n as int);
            assert(evens.len() as int == n as int / 2);
            assert(odds.len() as int == n as int / 2);
        }

        let ghost even_seq = evens@;
        let ghost odd_seq = odds@;
        let mut result: Vec<i32> = Vec::new();
        let mut j: usize = 0;

        while j < evens.len()
            invariant
                n == nums.len(),
                evens@ == even_seq,
                odds@ == odd_seq,
                evens.len() == odds.len(),
                evens.len() as int == n as int / 2,
                0 <= j <= evens.len(),
                forall |k: int| 0 <= k < evens.len() ==> evens[k] % 2 == 0,
                forall |k: int| 0 <= k < odds.len() ==> odds[k] % 2 != 0,
                result@ == Self::interleave(even_seq, odd_seq, j as int),
                result.len() == 2 * j,
                forall |k: int| 0 <= k < result.len() && k % 2 == 0 ==> result[k] % 2 == 0,
                forall |k: int| 0 <= k < result.len() && k % 2 != 0 ==> result[k] % 2 != 0,
            decreases evens.len() - j,
        {
            let even_v = evens[j];
            let odd_v = odds[j];
            result.push(even_v);
            result.push(odd_v);

            proof {
                assert(even_v % 2 == 0);
                assert(odd_v % 2 != 0);
                assert(result@ == Self::interleave(even_seq, odd_seq, j as int + 1));

                assert forall |k: int| 0 <= k < result.len() && k % 2 == 0 implies result[k] % 2 == 0 by {
                    if k < 2 * j as int {
                    } else {
                        assert(k == 2 * j as int);
                        assert(result[k] == even_v);
                    }
                }

                assert forall |k: int| 0 <= k < result.len() && k % 2 != 0 implies result[k] % 2 != 0 by {
                    if k < 2 * j as int {
                    } else {
                        assert(k == 2 * j as int + 1);
                        assert(result[k] == odd_v);
                    }
                }
            }

            j = j + 1;
        }

        proof {
            assert(result@ == Self::interleave(even_seq, odd_seq, evens.len() as int));
            assert(result.len() == n);
            assert forall |v: i32| Self::count(result@, v) == Self::count(nums@, v) by {
                Self::count_interleave(even_seq, odd_seq, v, evens.len() as int);
                Self::count_filter_split(nums@, v, n as int);
                assert(even_seq =~= even_seq.subrange(0, evens.len() as int));
                assert(odd_seq =~= odd_seq.subrange(0, odds.len() as int));
                assert(nums@ =~= nums@.subrange(0, n as int));
            }
        }

        result
    }
}

}
