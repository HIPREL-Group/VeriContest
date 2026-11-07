use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_valid_play(play: Seq<usize>, n: int) -> bool {
        play.len() == n
        && (forall |i: int| 0 <= i < n ==> (#[trigger] play[i] as int) < n)
        && (forall |i: int, j: int| 0 <= i < j < n ==> play[i] != play[j])
    }

    pub open spec fn alice_score(play: Seq<usize>, av: Seq<i32>, k: int) -> int
        decreases k
    {
        if k <= 0 { 0 }
        else if (k - 1) % 2 == 0 {
            av[play[k - 1] as int] as int + Self::alice_score(play, av, k - 1)
        } else {
            Self::alice_score(play, av, k - 1)
        }
    }

    pub open spec fn bob_score(play: Seq<usize>, bv: Seq<i32>, k: int) -> int
        decreases k
    {
        if k <= 0 { 0 }
        else if (k - 1) % 2 == 1 {
            bv[play[k - 1] as int] as int + Self::bob_score(play, bv, k - 1)
        } else {
            Self::bob_score(play, bv, k - 1)
        }
    }

    pub open spec fn swap_gain(
        play: Seq<usize>, av: Seq<i32>, bv: Seq<i32>, k: int, j: int,
    ) -> int {
        let sk = play[k] as int;
        let sj = play[j] as int;
        (av[sj] as int + bv[sj] as int) - (av[sk] as int + bv[sk] as int)
    }

    pub open spec fn is_optimal_play(
        play: Seq<usize>, av: Seq<i32>, bv: Seq<i32>, n: int,
    ) -> bool {
        forall |k: int, j: int|
            0 <= k < j < n && k % 2 != j % 2
            ==> Self::swap_gain(play, av, bv, k, j) <= 0
    }

    pub open spec fn sorted_by_combined_desc(
        indices: Seq<usize>,
        av: Seq<i32>,
        bv: Seq<i32>,
    ) -> bool {
        forall |i: int, j: int| 0 <= i < j < indices.len() ==>
            (av[indices[i] as int] + bv[indices[i] as int])
            >= (av[indices[j] as int] + bv[indices[j] as int])
    }

    pub open spec fn count_ge(av: Seq<i32>, bv: Seq<i32>, threshold: int, hi: int) -> int
        decreases hi
    {
        if hi <= 0 { 0 }
        else {
            (if (av[hi - 1] + bv[hi - 1]) as int >= threshold { 1int } else { 0int })
            + Self::count_ge(av, bv, threshold, hi - 1)
        }
    }

    pub open spec fn count_eq(av: Seq<i32>, bv: Seq<i32>, val: int, hi: int) -> int
        decreases hi
    {
        if hi <= 0 { 0 }
        else {
            (if (av[hi - 1] + bv[hi - 1]) as int == val { 1int } else { 0int })
            + Self::count_eq(av, bv, val, hi - 1)
        }
    }

    proof fn lemma_count_ge_zero(av: Seq<i32>, bv: Seq<i32>, hi: int)
        requires
            0 <= hi <= av.len(),
            av.len() == bv.len(),
            forall |i: int| 0 <= i < av.len() ==> 1 <= #[trigger] av[i] <= 100,
            forall |i: int| 0 <= i < bv.len() ==> 1 <= #[trigger] bv[i] <= 100,
        ensures
            Self::count_ge(av, bv, 201, hi) == 0,
        decreases hi
    {
        if hi > 0 {
            Self::lemma_count_ge_zero(av, bv, hi - 1);
        }
    }

    proof fn lemma_count_ge_all(av: Seq<i32>, bv: Seq<i32>, hi: int)
        requires
            0 <= hi <= av.len(),
            av.len() == bv.len(),
            forall |i: int| 0 <= i < av.len() ==> 1 <= #[trigger] av[i] <= 100,
            forall |i: int| 0 <= i < bv.len() ==> 1 <= #[trigger] bv[i] <= 100,
        ensures
            Self::count_ge(av, bv, 2, hi) == hi,
        decreases hi
    {
        if hi > 0 {
            Self::lemma_count_ge_all(av, bv, hi - 1);
        }
    }

    proof fn lemma_count_ge_split(av: Seq<i32>, bv: Seq<i32>, v: int, hi: int)
        requires
            0 <= hi <= av.len(),
            av.len() == bv.len(),
        ensures
            Self::count_ge(av, bv, v, hi) ==
                Self::count_ge(av, bv, v + 1, hi) + Self::count_eq(av, bv, v, hi),
        decreases hi
    {
        if hi > 0 {
            Self::lemma_count_ge_split(av, bv, v, hi - 1);
        }
    }

    proof fn lemma_count_ge_bounds(av: Seq<i32>, bv: Seq<i32>, threshold: int, hi: int)
        requires
            0 <= hi <= av.len(),
            av.len() == bv.len(),
        ensures
            0 <= Self::count_ge(av, bv, threshold, hi) <= hi,
        decreases hi
    {
        if hi > 0 {
            Self::lemma_count_ge_bounds(av, bv, threshold, hi - 1);
        }
    }

    pub fn stone_game_vi(alice_values: Vec<i32>, bob_values: Vec<i32>) -> (res: i32)
        requires
            alice_values.len() == bob_values.len(),
            1 <= alice_values.len() <= 100_000,
            forall |i: int| 0 <= i < alice_values.len() ==> 1 <= #[trigger] alice_values[i] <= 100,
            forall |i: int| 0 <= i < bob_values.len() ==> 1 <= #[trigger] bob_values[i] <= 100,
        ensures
            res == 1 || res == 0 || res == -1,
            exists |play: Seq<usize>|
                #[trigger] Self::is_valid_play(play, alice_values.len() as int)
                && Self::is_optimal_play(play, alice_values@, bob_values@, alice_values.len() as int)
                && {
                    let n = alice_values.len() as int;
                    let a_total = Self::alice_score(play, alice_values@, n);
                    let b_total = Self::bob_score(play, bob_values@, n);
                    (a_total > b_total ==> res == 1)
                    && (a_total < b_total ==> res == -1)
                    && (a_total == b_total ==> res == 0)
                },
    {
        let n = alice_values.len();
        let ghost av = alice_values@;
        let ghost bv = bob_values@;

        let mut indices: Vec<usize> = Vec::new();

        proof {
            Self::lemma_count_ge_zero(av, bv, n as int);
        }

        let mut v: usize = 200;

        while v >= 2
            invariant
                1 <= v <= 200,
                n == alice_values.len(),
                alice_values.len() == bob_values.len(),
                av == alice_values@,
                bv == bob_values@,
                1 <= n <= 100_000,
                forall |i: int| 0 <= i < n as int ==> 1 <= #[trigger] av[i] <= 100,
                forall |i: int| 0 <= i < n as int ==> 1 <= #[trigger] bv[i] <= 100,
                indices.len() as int == Self::count_ge(av, bv, (v + 1) as int, n as int),
                forall |m: int| 0 <= m < indices.len() ==> (#[trigger] indices@[m] as int) < n as int,
                forall |m: int, p: int| 0 <= m < p < indices.len() ==> indices@[m] != indices@[p],
                Self::sorted_by_combined_desc(indices@, av, bv),
                forall |m: int| 0 <= m < indices.len() ==>
                    (av[indices@[m] as int] + bv[indices@[m] as int]) as int > (v as int),
            decreases v
        {
            let ghost old_len = indices.len() as int;
            let mut i: usize = 0;

            while i < n
                invariant
                    0 <= i <= n,
                    n == alice_values.len(),
                    alice_values.len() == bob_values.len(),
                    av == alice_values@,
                    bv == bob_values@,
                    1 <= n <= 100_000,
                    2 <= v <= 200,
                    forall |ii: int| 0 <= ii < n as int ==> 1 <= #[trigger] av[ii] <= 100,
                    forall |ii: int| 0 <= ii < n as int ==> 1 <= #[trigger] bv[ii] <= 100,
                    old_len == Self::count_ge(av, bv, (v + 1) as int, n as int) as int,
                    indices.len() as int == old_len + Self::count_eq(av, bv, v as int, i as int),
                    forall |m: int| 0 <= m < indices.len() ==> (#[trigger] indices@[m] as int) < n as int,
                    forall |m: int, p: int| 0 <= m < p < indices.len() ==> indices@[m] != indices@[p],
                    Self::sorted_by_combined_desc(indices@, av, bv),
                    forall |m: int| 0 <= m < indices.len() ==>
                        (av[indices@[m] as int] + bv[indices@[m] as int]) as int > (v as int)
                        || ((av[indices@[m] as int] + bv[indices@[m] as int]) as int == (v as int)
                            && (indices@[m] as int) < (i as int)),
                decreases n - i
            {
                let ghost old_indices = indices@;
                let ghost old_count = Self::count_eq(av, bv, v as int, i as int);

                if alice_values[i] + bob_values[i] == v as i32 {
                    proof {
                        Self::lemma_count_ge_bounds(av, bv, (v + 1) as int, n as int);
                        Self::lemma_count_ge_bounds(av, bv, 2, n as int);
                    }

                    indices.push(i);

                    proof {
                        assert forall |m: int, p: int| 0 <= m < p < indices.len()
                            implies indices@[m] != indices@[p] by {
                            if p == old_indices.len() as int {
                                assert(indices@[p] == i as usize);
                                if m < old_indices.len() as int {
                                    assert(indices@[m] == old_indices[m]);
                                    if (av[old_indices[m] as int] + bv[old_indices[m] as int]) as int > (v as int) {
                                        assert(old_indices[m] != i as usize);
                                    } else {
                                        assert((old_indices[m] as int) < (i as int));
                                        assert(old_indices[m] != i as usize);
                                    }
                                }
                            }
                        };

                        assert forall |ii: int, jj: int| 0 <= ii < jj < indices.len()
                            implies (av[indices@[ii] as int] + bv[indices@[ii] as int])
                                >= (av[indices@[jj] as int] + bv[indices@[jj] as int]) by {
                            if jj == old_indices.len() as int {
                                assert(indices@[jj] == i as usize);
                                assert((av[i as int] + bv[i as int]) as int == (v as int));
                                assert(indices@[ii] == old_indices[ii]);
                                assert((av[old_indices[ii] as int] + bv[old_indices[ii] as int]) as int >= (v as int));
                            }
                        };

                        assert(indices.len() as int == old_len + old_count + 1);
                        assert(Self::count_eq(av, bv, v as int, (i + 1) as int)
                            == old_count + 1);
                    }
                } else {
                    proof {
                        assert(Self::count_eq(av, bv, v as int, (i + 1) as int)
                            == old_count);
                    }
                }
                i += 1;
            }

            proof {
                Self::lemma_count_ge_split(av, bv, v as int, n as int);
                assert(indices.len() as int ==
                    Self::count_ge(av, bv, (v + 1) as int, n as int)
                    + Self::count_eq(av, bv, v as int, n as int));
                assert(Self::count_ge(av, bv, v as int, n as int)
                    == Self::count_ge(av, bv, (v + 1) as int, n as int)
                    + Self::count_eq(av, bv, v as int, n as int));

                assert forall |m: int| 0 <= m < indices.len()
                    implies (av[indices@[m] as int] + bv[indices@[m] as int]) as int > ((v - 1) as int) by {
                    assert((av[indices@[m] as int] + bv[indices@[m] as int]) as int >= (v as int));
                };
            }

            v -= 1;
        }

        proof {
            Self::lemma_count_ge_all(av, bv, n as int);
            assert(indices.len() as int == Self::count_ge(av, bv, 2, n as int));
            assert(Self::count_ge(av, bv, 2, n as int) == n as int);
            assert(indices.len() == n);
            assert(Self::is_valid_play(indices@, n as int));

            assert forall |k: int, j: int|
                0 <= k < j < n as int && k % 2 != j % 2
                implies Self::swap_gain(indices@, av, bv, k, j) <= 0 by {
            };
            assert(Self::is_optimal_play(indices@, av, bv, n as int));
        }

        let mut alice_total: i32 = 0;
        let mut bob_total: i32 = 0;
        let mut k: usize = 0;

        while k < n
            invariant
                0 <= k <= n,
                n == alice_values.len(),
                n == indices.len(),
                alice_values.len() == bob_values.len(),
                av == alice_values@,
                bv == bob_values@,
                1 <= n <= 100_000,
                forall |ii: int| 0 <= ii < n as int ==> 1 <= #[trigger] av[ii] <= 100,
                forall |ii: int| 0 <= ii < n as int ==> 1 <= #[trigger] bv[ii] <= 100,
                Self::is_valid_play(indices@, n as int),
                Self::sorted_by_combined_desc(indices@, av, bv),
                Self::is_optimal_play(indices@, av, bv, n as int),
                alice_total as int == Self::alice_score(indices@, av, k as int),
                bob_total as int == Self::bob_score(indices@, bv, k as int),
                0 <= alice_total <= (k as i32) * 100,
                0 <= bob_total <= (k as i32) * 100,
            decreases n - k
        {
            if k % 2 == 0 {
                alice_total += alice_values[indices[k]];
            } else {
                bob_total += bob_values[indices[k]];
            }
            k += 1;
        }

        proof {
            let play = indices@;
            assert(Self::is_valid_play(play, n as int));
            assert(Self::is_optimal_play(play, av, bv, n as int));
            assert(alice_total as int == Self::alice_score(play, av, n as int));
            assert(bob_total as int == Self::bob_score(play, bv, n as int));
        }

        if alice_total > bob_total {
            1
        } else if alice_total < bob_total {
            -1
        } else {
            0
        }
    }
}

}
