use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_occurrences(s: Seq<i32>, value: i32) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            Self::count_occurrences(s.drop_last(), value) +
                if s.last() == value { 1 as nat } else { 0 as nat }
        }
    }

    proof fn lemma_count_single(s: Seq<i32>, value: i32)
        requires 
            s.len() == 1,
        ensures 
            Self::count_occurrences(s, value) == if s[0] == value { 1nat } else { 0nat }, 
    {
        assert(s.drop_last() =~= Seq::<i32>::empty());
        assert(Self::count_occurrences(Seq::<i32>::empty(), value) == 0nat);
    }

    proof fn lemma_count_concat(a: Seq<i32>, b: Seq<i32>, value: i32)
        ensures 
            Self::count_occurrences(a + b, value) ==
                Self::count_occurrences(a, value) + Self::count_occurrences(b, value), 
        decreases 
            b.len(), 
    {
        if b.len() == 0 {
            assert(a + b =~= a);
        } else {
            let b_init = b.drop_last();
            assert((a + b).drop_last() =~= a + b_init);
            Self::lemma_count_concat(a, b_init, value);
        }
    }

    proof fn lemma_count_pair(s: Seq<i32>, i: int, value: i32)
        requires
            0 <= i < i + 1 < s.len(),
            s[i] == value,
            s[i + 1] == value,
        ensures
            Self::count_occurrences(s.subrange(i, i + 2), value) == 2nat
    {
        let sub = s.subrange(i, i + 2);
        let singleton = sub.drop_last();
        assert(singleton.drop_last() =~= Seq::<i32>::empty());
        assert(Self::count_occurrences(Seq::<i32>::empty(), value) == 0nat);
        assert(Self::count_occurrences(singleton, value) == 1nat);
    }

    proof fn lemma_count_zero_if_absent(s: Seq<i32>, v: i32)
        requires 
            forall |j: int| 0 <= j < s.len() ==> s[j] != v, 
        ensures 
            Self::count_occurrences(s, v) == 0, 
        decreases s.len(),
    {
        if s.len() > 0 {
            assert(s.last() != v);
            assert forall |j: int| 0 <= j < s.drop_last().len() implies s.drop_last()[j] != v by {
                assert(s.drop_last()[j] == s[j]);
            };
            Self::lemma_count_zero_if_absent(s.drop_last(), v);
        }
    }

    proof fn lemma_count_positive_if_present(s: Seq<i32>, v: i32, idx: int)
        requires 0 <= idx < s.len(), s[idx] == v
        ensures Self::count_occurrences(s, v) >= 1
        decreases s.len()
    {
        if idx == s.len() - 1 {
            assert(s.last() == v);
        } else {
            assert(s.drop_last()[idx] == v);
            Self::lemma_count_positive_if_present(s.drop_last(), v, idx);
        }
    }

    pub fn single_non_duplicate(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100_000,
            nums.len() % 2 == 1,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> #[trigger] nums[i] <= #[trigger] nums[j],
            exists |single: i32| {
                &&& Self::count_occurrences(nums@, single) == 1
                &&& forall |v: i32| v != single && (exists |i: int| 0 <= i < nums@.len() && nums@[i] == v)
                        ==> #[trigger] Self::count_occurrences(nums@, v) == 2
            },
        ensures
            Self::count_occurrences(nums@, res) == 1,
    {
        let n = nums.len();
        let mut i: usize = 0;
        while i + 1 < n
            invariant
                1 <= nums.len() <= 100_000,
                nums.len() % 2 == 1,
                forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
                forall |i: int, j: int| 0 <= i < j < nums.len() ==> #[trigger] nums[i] <= #[trigger] nums[j],
                exists |single: i32| {
                    &&& Self::count_occurrences(nums@, single) == 1
                    &&& forall |v: i32| v != single && (exists |i: int| 0 <= i < nums@.len() && nums@[i] == v)
                            ==> #[trigger] Self::count_occurrences(nums@, v) == 2
                },
                i % 2 == 0,
                i < n,
                n == nums.len(),
                i == 0 || nums@[(i as int) - 1] < nums@[i as int],
            decreases n - (i + 1),
        {
            if nums[i] != nums[i + 1] {
                let result = nums[i];
                proof {
                    let s = nums@;
                    let idx = i as int;
                    let v = result;

                    let pre = s.subrange(0, idx);
                    assert(Self::count_occurrences(pre, v) == 0) by {
                        if idx == 0 {
                            assert(pre =~= Seq::<i32>::empty());
                        } else {
                            assert forall |j: int| 0 <= j < pre.len() implies pre[j] != v by {
                                assert(pre[j] == s[j]);
                                assert(s[j] <= s[idx - 1]);
                            };
                            Self::lemma_count_zero_if_absent(pre, v);
                        }
                    };

                    let suf = s.subrange(idx + 1, s.len() as int);
                    assert(Self::count_occurrences(suf, v) == 0) by {
                        assert forall |j: int| 0 <= j < suf.len() implies suf[j] != v by {
                            assert(suf[j] == s[idx + 1 + j]);
                            assert(s[idx + 1 + j] >= s[idx + 1]);
                            assert(s[idx + 1] > v);
                        };
                        Self::lemma_count_zero_if_absent(suf, v);
                    };

                    let mid = s.subrange(idx, idx + 1);
                    assert(Self::count_occurrences(mid, v) == 1) by {
                        Self::lemma_count_single(mid, v);
                    };

                    assert(s =~= pre + s.subrange(idx, s.len() as int));
                    assert(s.subrange(idx, s.len() as int) =~= mid + suf);
                    Self::lemma_count_concat(pre, s.subrange(idx, s.len() as int), v);
                    Self::lemma_count_concat(mid, suf, v);
                    assert(Self::count_occurrences(s, v) == 1);
                }
                return result;
            }

            proof {
                let s = nums@;
                let idx = i as int;
                let v = s[idx]; 
                let pre = s.subrange(0, idx);
                
                assert(Self::count_occurrences(pre, v) == 0) by {
                    if idx == 0 {
                        assert(pre =~= Seq::<i32>::empty());
                    } else {
                        assert forall |j: int| 0 <= j < pre.len() implies pre[j] != v by {
                            assert(pre[j] == s[j]);
                            assert(s[j] <= s[idx - 1]);
                        };
                        Self::lemma_count_zero_if_absent(pre, v);
                    }
                };

                let pair = s.subrange(idx, idx + 2);
                assert(Self::count_occurrences(pair, v) == 2) by {
                    Self::lemma_count_pair(s, idx, v);
                };

                let suf = s.subrange(idx + 2, s.len() as int);
                assert(s =~= pre + s.subrange(idx, s.len() as int));
                assert(s.subrange(idx, s.len() as int) =~= pair + suf);
                Self::lemma_count_concat(pre, s.subrange(idx, s.len() as int), v);
                Self::lemma_count_concat(pair, suf, v);
                assert(Self::count_occurrences(s, v) == 2 + Self::count_occurrences(suf, v));

                assert(s[idx + 2] != v) by {
                    if s[idx + 2] == v {
                        assert(suf[0] == v);
                        Self::lemma_count_positive_if_present(suf, v, 0);
                        assert(false);
                    }
                };
            }
            i = i + 2;
        }
        proof {
            let s = nums@;
            let idx = i as int;
            let v = s[idx];
            let pre = s.subrange(0, idx);

            assert(Self::count_occurrences(pre, v) == 0) by {
                if idx == 0 {
                    assert(pre =~= Seq::<i32>::empty());
                } else {
                    assert forall |j: int| 0 <= j < pre.len() implies pre[j] != v by {
                        assert(pre[j] == s[j]);
                        assert(s[j] <= s[idx - 1]);
                    };
                    Self::lemma_count_zero_if_absent(pre, v);
                }
            };

            let suf = s.subrange(idx + 1, s.len() as int);
            assert(suf =~= Seq::<i32>::empty());
            assert(Self::count_occurrences(suf, v) == 0);

            let mid = s.subrange(idx, idx + 1);
            assert(Self::count_occurrences(mid, v) == 1) by {
                Self::lemma_count_single(mid, v);
            };

            assert(s =~= pre + s.subrange(idx, s.len() as int));
            assert(s.subrange(idx, s.len() as int) =~= mid + suf);
            Self::lemma_count_concat(pre, s.subrange(idx, s.len() as int), v);
            Self::lemma_count_concat(mid, suf, v);
            assert(Self::count_occurrences(s, v) == 1);
        }
        nums[i]
    }
}

}