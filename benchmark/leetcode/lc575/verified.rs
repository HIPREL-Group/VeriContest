use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn has_val(s: Seq<i32>, v: i32) -> bool {
        exists|i: int| 0 <= i < s.len() && s[i] == v
    }

    pub open spec fn num_distinct(s: Seq<i32>) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0int
        } else {
            let rest = Self::num_distinct(s.drop_last());
            if Self::has_val(s.drop_last(), s.last()) {
                rest
            } else {
                rest + 1
            }
        }
    }

    proof fn lemma_has_val_push(s: Seq<i32>, v: i32, w: i32)
        ensures Self::has_val(s.push(v), w) == (Self::has_val(s, w) || w == v),
    {
        if Self::has_val(s, w) {
            let wit = choose|idx: int| 0 <= idx < s.len() && s[idx] == w;
            assert(0 <= wit < s.push(v).len() && s.push(v)[wit] == w);
        }
        if w == v {
            assert(0 <= s.len() < s.push(v).len() && s.push(v)[s.len() as int] == w);
        }
        if Self::has_val(s.push(v), w) {
            let wit = choose|idx: int| 0 <= idx < s.push(v).len() && s.push(v)[idx] == w;
            if wit < s.len() {
                assert(s[wit] == w);
            }
        }
    }

    proof fn lemma_distinct_push(s: Seq<i32>, v: i32)
        ensures Self::num_distinct(s.push(v)) ==
            Self::num_distinct(s) + (if Self::has_val(s, v) { 0int } else { 1int }),
    {
        assert(s.push(v).drop_last() =~= s);
        assert(s.push(v).last() == v);
    }

    proof fn lemma_distinct_nonneg(s: Seq<i32>)
        ensures Self::num_distinct(s) >= 0,
        decreases s.len(),
    {
        if s.len() > 0 {
            Self::lemma_distinct_nonneg(s.drop_last());
        }
    }

    proof fn lemma_distinct_le_len(s: Seq<i32>)
        ensures Self::num_distinct(s) <= s.len(),
        decreases s.len(),
    {
        if s.len() > 0 {
            Self::lemma_distinct_le_len(s.drop_last());
        }
    }

    pub fn distribute_candies(candy_type: Vec<i32>) -> (res: i32)
        requires
            candy_type.len() % 2 == 0,
            2 <= candy_type.len() <= 10_000,
            forall|i: int| 0 <= i < candy_type.len() ==>
                -100_000 <= #[trigger] candy_type[i] <= 100_000,
        ensures
            res == if Self::num_distinct(candy_type@) <= candy_type.len() / 2 {
                Self::num_distinct(candy_type@) as i32
            } else {
                (candy_type.len() / 2) as i32
            },
    {
        let mut seen: Vec<bool> = Vec::new();
        let mut fill_idx = 0usize;
        while fill_idx < 200001usize
            invariant
                fill_idx <= 200001,
                seen@.len() == fill_idx,
                forall|k: int| 0 <= k < fill_idx ==> seen@[k] == false,
            decreases 200001usize - fill_idx,
        {
            seen.push(false);
            fill_idx += 1;
        }

        let mut distinct = 0i32;
        let n = candy_type.len();
        let ghost ct = candy_type@;
        let mut i = 0usize;

        assert(Self::num_distinct(ct.take(0int)) == 0) by {
            assert(ct.take(0int) =~= Seq::<i32>::empty());
            assert(Seq::<i32>::empty().len() == 0);
            reveal_with_fuel(Solution::num_distinct, 1);
        };

        while i < n
            invariant
                i <= n,
                n == candy_type.len(),
                ct == candy_type@,
                seen@.len() == 200001,
                n <= 10_000,
                0 <= distinct,
                distinct <= i as i32,
                distinct == Self::num_distinct(ct.take(i as int)),
                forall|k: int| 0 <= k < candy_type.len() ==>
                    -100_000 <= #[trigger] candy_type@[k] <= 100_000,
                forall|j: int| 0 <= j < 200001 ==> (seen@[j] == Self::has_val(ct.take(i as int), (j - 100_000) as i32)),
            decreases n - i,
        {
            let ci = candy_type[i];
            let offset = (ci as i64 + 100_000i64) as usize;

            assert(0 <= offset < 200001) by {
                assert(-100_000 <= ci as int <= 100_000);
                assert(offset as int == ci as int + 100_000);
            };

            let ghost sub_prev = ct.take(i as int);
            let ghost sub_next = ct.take(i as int + 1);
            assert(sub_next =~= sub_prev.push(ci));

            if !seen[offset] {
                let ghost old_seen_seq: Seq<bool> = seen@;
                proof {
                    assert(!Self::has_val(sub_prev, ci)) by {
                        assert(seen@[offset as int] == false);
                        assert(offset as int == ci as int + 100_000);
                        assert((offset as int - 100_000) as i32 == ci) by {
                            assert(offset as int - 100_000 == ci as int);
                        };
                    };
                    Self::lemma_distinct_push(sub_prev, ci);
                    assert(Self::num_distinct(sub_next) == Self::num_distinct(sub_prev) + 1);
                }
                seen.set(offset, true);
                distinct += 1;
                proof {
                    assert forall|j: int| 0 <= j < 200001 implies
                        seen@[j] == Self::has_val(sub_next, (j - 100_000) as i32)
                    by {
                        if j == offset as int {
                            assert(seen@[j] == true);
                            assert(Self::has_val(sub_next, ci)) by {
                                assert(sub_next.len() > 0);
                                assert(sub_next.last() == ci);
                            };
                            assert((j - 100_000) as i32 == ci) by {
                                assert(j == ci as int + 100_000);
                            };
                        } else {
                            assert(seen@[j] == old_seen_seq[j]);
                            let w = (j - 100_000) as i32;
                            assert(w != ci) by {
                                assert(j != offset as int);
                                assert(j != ci as int + 100_000);
                            };
                            Self::lemma_has_val_push(sub_prev, ci, w);
                            assert(Self::has_val(sub_next, w) == Self::has_val(sub_prev, w));
                        }
                    };
                }
            } else {
                proof {
                    assert(Self::has_val(sub_prev, ci)) by {
                        assert(seen@[offset as int] == true);
                        assert((offset as int - 100_000) as i32 == ci) by {
                            assert(offset as int - 100_000 == ci as int);
                        };
                    };
                    Self::lemma_distinct_push(sub_prev, ci);
                    assert(Self::num_distinct(sub_next) == Self::num_distinct(sub_prev));
                    assert forall|j: int| 0 <= j < 200001 implies
                        seen@[j] == Self::has_val(sub_next, (j - 100_000) as i32)
                    by {
                        let w = (j - 100_000) as i32;
                        Self::lemma_has_val_push(sub_prev, ci, w);
                        assert(Self::has_val(sub_next, w) == (Self::has_val(sub_prev, w) || w == ci));
                        assert(Self::has_val(sub_prev, ci));
                        if w == ci {
                            assert(Self::has_val(sub_next, w));
                            assert(seen@[j] == Self::has_val(sub_prev, w));
                        } else {
                            assert(Self::has_val(sub_next, w) == Self::has_val(sub_prev, w));
                        }
                    };
                }
            }
            i += 1;
        }

        proof {
            assert(ct.take(n as int) =~= ct);
            Self::lemma_distinct_nonneg(ct);
            Self::lemma_distinct_le_len(ct);
        }

        let half = (n / 2) as i32;
        if distinct <= half { distinct } else { half }
    }
}

} 
