use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;
















impl Solution {
    pub open spec fn min2(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    
    pub open spec fn min_col_cost(cost: Seq<Seq<i32>>, j: int, i: int) -> int
        decreases cost.len() - i,
    {
        if i >= cost.len() {
            101int
        } else {
            Self::min2(cost[i][j] as int, Self::min_col_cost(cost, j, i + 1))
        }
    }

    
    pub open spec fn unconnected_cost(cost: Seq<Seq<i32>>, n: int, mask: u32, j: int) -> int
        decreases n - j,
    {
        if j >= n {
            0int
        } else if (mask & (1u32 << (j as u32))) == 0u32 {
            Self::min_col_cost(cost, j, 0) + Self::unconnected_cost(cost, n, mask, j + 1)
        } else {
            Self::unconnected_cost(cost, n, mask, j + 1)
        }
    }

    
    
    
    pub open spec fn dp(cost: Seq<Seq<i32>>, m: int, n: int, row: int, mask: u32, j: int) -> int
        decreases m - row, n - j,
    {
        if row >= m {
            Self::unconnected_cost(cost, n, mask, 0)
        } else if j >= n {
            100_000int
        } else {
            let new_mask = (mask | (1u32 << (j as u32)));
            let connect_j = cost[row][j] as int + Self::dp(cost, m, n, row + 1, new_mask, 0);
            let skip_j = Self::dp(cost, m, n, row, mask, j + 1);
            Self::min2(connect_j, skip_j)
        }
    }

    proof fn lemma_min2_assoc(a: int, b: int, c: int)
        ensures
            Self::min2(Self::min2(a, b), c) == Self::min2(a, Self::min2(b, c)),
    {
    }

    proof fn lemma_min_col_cost_bounded(cost: Seq<Seq<i32>>, j: int, i: int)
        requires
            cost.len() >= 1,
            0 <= j,
            0 <= i,
            i < cost.len(),
            forall|r: int|
                0 <= r < cost.len() ==> j < (#[trigger] cost[r]).len(),
            forall|r: int|
                0 <= r < cost.len() ==> 0 <= (#[trigger] cost[r])[j] <= 100,
        ensures
            0 <= Self::min_col_cost(cost, j, i) <= 100,
        decreases cost.len() - i,
    {
        assert(0 <= cost[i][j] <= 100);
        if i + 1 < cost.len() {
            Self::lemma_min_col_cost_bounded(cost, j, i + 1);
            assert(0 <= Self::min_col_cost(cost, j, i + 1) <= 100);
        } else {
            assert(Self::min_col_cost(cost, j, i + 1) == 101int);
        }
        assert(Self::min_col_cost(cost, j, i) == Self::min2(
            cost[i][j] as int,
            Self::min_col_cost(cost, j, i + 1),
        ));
    }

    proof fn lemma_unconnected_cost_bounded(cost: Seq<Seq<i32>>, n: int, mask: u32, j: int)
        requires
            0 <= j <= n,
            n <= 12,
            cost.len() >= 1,
            forall|r: int|
                0 <= r < cost.len() ==> (#[trigger] cost[r]).len() == n,
            forall|r: int, c: int|
                #![trigger cost[r][c]]
                0 <= r < cost.len() && 0 <= c < n ==> 0 <= cost[r][c] <= 100,
        ensures
            0 <= Self::unconnected_cost(cost, n, mask, j) <= (n - j) * 100,
        decreases n - j,
    {
        if j < n {
            Self::lemma_unconnected_cost_bounded(cost, n, mask, j + 1);
            if (mask & (1u32 << (j as u32))) == 0u32 {
                assert forall|r: int| 0 <= r < cost.len() implies j < (#[trigger] cost[r]).len()
                by {};
                assert forall|r: int|
                    0 <= r < cost.len()
                implies
                    0 <= (#[trigger] cost[r])[j] <= 100
                by {
                    assert(0 <= cost[r][j] <= 100);
                };
                Self::lemma_min_col_cost_bounded(cost, j, 0);
            }
        }
    }

    proof fn lemma_dp_bounded(
        cost: Seq<Seq<i32>>,
        m: int,
        n: int,
        row: int,
        mask: u32,
        j: int,
    )
        requires
            m == cost.len(),
            1 <= m <= 12,
            1 <= n <= 12,
            0 <= row <= m,
            0 <= j <= n,
            forall|r: int|
                0 <= r < m ==> (#[trigger] cost[r]).len() == n,
            forall|r: int, c: int|
                #![trigger cost[r][c]]
                0 <= r < m && 0 <= c < n ==> 0 <= cost[r][c] <= 100,
        ensures
            Self::dp(cost, m, n, row, mask, j) <= 100_000,
            Self::dp(cost, m, n, row, mask, j) >= 0,
        decreases m - row, n - j,
    {
        if row >= m {
            Self::lemma_unconnected_cost_bounded(cost, n, mask, 0);
        } else if j >= n {
        } else {
            Self::lemma_dp_bounded(
                cost,
                m,
                n,
                row + 1,
                mask | (1u32 << (j as u32)),
                0,
            );
            Self::lemma_dp_bounded(cost, m, n, row, mask, j + 1);
        }
    }

    proof fn lemma_min_col_cost_step(
        cost: Seq<Seq<i32>>,
        j: int,
        i: int,
        mc: int,
    )
        requires
            cost.len() >= 1,
            0 <= j,
            0 <= i <= cost.len(),
            forall|r: int|
                0 <= r < cost.len() ==> j < (#[trigger] cost[r]).len(),
            forall|r: int|
                0 <= r < cost.len() ==> 0 <= (#[trigger] cost[r])[j] <= 100,
            0 <= mc <= 100,
            Self::min2(mc, Self::min_col_cost(cost, j, i)) == Self::min_col_cost(cost, j, 0),
        ensures
            i < cost.len() ==> Self::min2(
                Self::min2(mc, cost[i][j] as int),
                Self::min_col_cost(cost, j, i + 1),
            ) == Self::min_col_cost(cost, j, 0),
    {
        if i < cost.len() {
            Self::lemma_min2_assoc(mc, cost[i][j] as int, Self::min_col_cost(cost, j, i + 1));
        }
    }

    #[verifier::spinoff_prover]
    pub fn connect_two_groups(cost: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= cost.len() <= 12,
            forall|i: int|
                0 <= i < cost.len() ==> (#[trigger] cost[i])@.len() == cost[0]@.len(),
            1 <= cost[0]@.len() <= 12,
            cost.len() >= cost[0]@.len(),
            forall|i: int, j: int|
                #![trigger cost[i]@[j]]
                0 <= i < cost.len() && 0 <= j < cost[0]@.len()
                    ==> 0 <= cost[i]@[j] <= 100,
        ensures
            result as int == Self::dp(
                Seq::new(cost.len() as nat, |i: int| cost[i]@),
                cost.len() as int,
                cost[0]@.len() as int,
                0,
                0u32,
                0,
            ),
    {
        let m = cost.len();
        let n = cost[0].len();
        let total_masks: usize = 1usize << n;

        let ghost cost_deep: Seq<Seq<i32>> = Seq::new(
            cost.len() as nat,
            |i: int| cost@[i]@,
        );
        let ghost m_int: int = m as int;
        let ghost n_int: int = n as int;

        proof {
            assert(total_masks <= 4096) by (bit_vector)
                requires
                    total_masks == 1usize << n,
                    1usize <= n <= 12usize,
            ;
            assert(total_masks >= 2) by (bit_vector)
                requires
                    total_masks == 1usize << n,
                    1usize <= n <= 12usize,
            ;
            assert forall|r: int|
                0 <= r < m_int
            implies
                (#[trigger] cost_deep[r]).len() == n_int
            by {
                assert(cost_deep[r] == cost@[r]@);
                assert(cost@[r]@.len() == cost[r]@.len());
            };
            assert forall|r: int, c: int|
                #![trigger cost_deep[r][c]]
                0 <= r < m_int && 0 <= c < n_int
            implies
                0 <= cost_deep[r][c] <= 100
            by {
                assert(cost_deep[r] == cost@[r]@);
                assert(cost@[r]@[c] == cost[r]@[c]);
            };
        }

        let mut min_cost: Vec<i32> = Vec::new();
        let mut jj: usize = 0;
        while jj < n
            invariant
                0 <= jj <= n,
                n == cost[0]@.len(),
                m == cost.len(),
                1 <= m <= 12,
                1 <= n <= 12,
                min_cost.len() == jj,
                cost_deep == Seq::new(cost.len() as nat, |i: int| cost@[i]@),
                m_int == m as int,
                n_int == n as int,
                cost_deep.len() == m as nat,
                forall|r: int|
                    0 <= r < m_int ==> (#[trigger] cost_deep[r]).len() == n_int,
                forall|r: int, c: int|
                    #![trigger cost_deep[r][c]]
                    0 <= r < m_int && 0 <= c < n_int ==> 0 <= cost_deep[r][c] <= 100,
                forall|i: int|
                    0 <= i < cost.len() ==> (#[trigger] cost[i])@.len() == cost[0]@.len(),
                forall|i: int, j: int|
                    #![trigger cost[i]@[j]]
                    0 <= i < cost.len() && 0 <= j < cost[0]@.len()
                        ==> 0 <= cost[i]@[j] <= 100,
                forall|k: int|
                    0 <= k < jj as int
                        ==> (#[trigger] min_cost@[k]) as int
                            == Self::min_col_cost(cost_deep, k, 0),
                forall|k: int|
                    0 <= k < jj as int ==> 0 <= #[trigger] min_cost@[k] <= 100,
            decreases n - jj,
        {
            let mut mc: i32 = cost[0][jj];
            let mut ii: usize = 1;

            proof {
                assert(cost_deep[0int][jj as int] == cost[0]@[jj as int]);
                assert(mc as int == cost_deep[0int][jj as int] as int);
                assert(Self::min2(mc as int, Self::min_col_cost(cost_deep, jj as int, 1))
                    == Self::min_col_cost(cost_deep, jj as int, 0));
            }

            while ii < m
                invariant
                    1 <= ii <= m,
                    m == cost.len(),
                    n == cost[0]@.len(),
                    1 <= m <= 12,
                    1 <= n <= 12,
                    0 <= jj < n,
                    cost_deep == Seq::new(cost.len() as nat, |i: int| cost@[i]@),
                    m_int == m as int,
                    n_int == n as int,
                    cost_deep.len() == m as nat,
                    forall|r: int|
                        0 <= r < m_int ==> (#[trigger] cost_deep[r]).len() == n_int,
                    forall|r: int, c: int|
                        #![trigger cost_deep[r][c]]
                        0 <= r < m_int && 0 <= c < n_int ==> 0 <= cost_deep[r][c] <= 100,
                    forall|i: int|
                        0 <= i < cost.len()
                            ==> (#[trigger] cost[i])@.len() == cost[0]@.len(),
                    forall|i: int, j: int|
                        #![trigger cost[i]@[j]]
                        0 <= i < cost.len() && 0 <= j < cost[0]@.len()
                            ==> 0 <= cost[i]@[j] <= 100,
                    0 <= mc <= 100,
                    Self::min2(mc as int, Self::min_col_cost(cost_deep, jj as int, ii as int))
                        == Self::min_col_cost(cost_deep, jj as int, 0),
                decreases m - ii,
            {
                proof {
                    assert(cost_deep[ii as int][jj as int] == cost[ii as int]@[jj as int]);
                    assert forall|r: int|
                        0 <= r < cost_deep.len()
                    implies
                        (jj as int) < (#[trigger] cost_deep[r]).len()
                    by {};
                    assert forall|r: int|
                        0 <= r < cost_deep.len()
                    implies
                        0 <= (#[trigger] cost_deep[r])[jj as int] <= 100
                    by {
                        assert(0 <= cost_deep[r][jj as int] <= 100);
                    };
                    Self::lemma_min_col_cost_step(
                        cost_deep,
                        jj as int,
                        ii as int,
                        mc as int,
                    );
                }
                if cost[ii][jj] < mc {
                    mc = cost[ii][jj];
                }
                ii = ii + 1;
            }

            proof {
                assert(Self::min_col_cost(cost_deep, jj as int, m_int) == 101int);
                assert(0 <= mc <= 100);
                assert(Self::min2(mc as int, 101int) == mc as int);
            }

            min_cost.push(mc);
            jj = jj + 1;
        }

        let mut dp: Vec<i32> = Vec::new();
        let mut mask: usize = 0;
        while mask < total_masks
            invariant
                0 <= mask <= total_masks,
                total_masks == 1usize << n,
                total_masks <= 4096,
                1 <= n <= 12,
                1 <= m <= 12,
                m == cost.len(),
                n == cost[0]@.len(),
                dp.len() == mask,
                min_cost.len() == n,
                cost_deep == Seq::new(cost.len() as nat, |i: int| cost@[i]@),
                n_int == n as int,
                m_int == m as int,
                forall|k: int|
                    0 <= k < n as int
                        ==> (#[trigger] min_cost@[k]) as int
                            == Self::min_col_cost(cost_deep, k, 0),
                forall|k: int|
                    0 <= k < n as int ==> 0 <= #[trigger] min_cost@[k] <= 100,
                forall|r: int, c: int|
                    #![trigger cost_deep[r][c]]
                    0 <= r < m_int && 0 <= c < n_int ==> 0 <= cost_deep[r][c] <= 100,
                forall|r: int|
                    0 <= r < m_int
                        ==> (#[trigger] cost_deep[r]).len() == n_int,
                forall|idx: int|
                    0 <= idx < mask as int
                        ==> (#[trigger] dp@[idx]) as int
                            == Self::unconnected_cost(
                                cost_deep,
                                n_int,
                                idx as u32,
                                0,
                            ),
                forall|idx: int|
                    0 <= idx < mask as int ==> 0 <= #[trigger] dp@[idx] <= n_int * 100,
            decreases total_masks - mask,
        {
            let mut uc: i32 = 0;
            let mut j: usize = 0;

            while j < n
                invariant
                    0 <= j <= n,
                    1 <= n <= 12,
                    0 <= mask < total_masks,
                    total_masks <= 4096,
                    min_cost.len() == n,
                    cost_deep == Seq::new(cost.len() as nat, |i: int| cost@[i]@),
                    n_int == n as int,
                    forall|k: int|
                        0 <= k < n as int
                            ==> (#[trigger] min_cost@[k]) as int
                                == Self::min_col_cost(cost_deep, k, 0),
                    forall|k: int|
                        0 <= k < n as int ==> 0 <= #[trigger] min_cost@[k] <= 100,
                    0 <= uc <= (j as int) * 100,
                    uc as int + Self::unconnected_cost(
                        cost_deep,
                        n_int,
                        mask as u32,
                        j as int,
                    ) == Self::unconnected_cost(cost_deep, n_int, mask as u32, 0),
                decreases n - j,
            {
                if ((mask as u32) & (1u32 << (j as u32))) == 0u32 {
                    uc = uc + min_cost[j];
                }
                j = j + 1;
            }

            proof {
                assert(Self::unconnected_cost(cost_deep, n_int, mask as u32, n_int) == 0int);
            }

            dp.push(uc);
            mask = mask + 1;
        }

        let mut row: usize = m;
        while row > 0
            invariant
                0 <= row <= m,
                m == cost.len(),
                n == cost[0]@.len(),
                1 <= m <= 12,
                1 <= n <= 12,
                total_masks == 1usize << n,
                total_masks <= 4096,
                total_masks >= 2,
                dp.len() == total_masks,
                cost_deep == Seq::new(cost.len() as nat, |i: int| cost@[i]@),
                m_int == m as int,
                n_int == n as int,
                forall|i: int|
                    0 <= i < cost.len()
                        ==> (#[trigger] cost[i])@.len() == cost[0]@.len(),
                forall|i: int, j: int|
                    #![trigger cost[i]@[j]]
                    0 <= i < cost.len() && 0 <= j < cost[0]@.len()
                        ==> 0 <= cost[i]@[j] <= 100,
                forall|r: int, c: int|
                    #![trigger cost_deep[r][c]]
                    0 <= r < m_int && 0 <= c < n_int ==> 0 <= cost_deep[r][c] <= 100,
                forall|r: int|
                    0 <= r < m_int
                        ==> (#[trigger] cost_deep[r]).len() == n_int,
                forall|idx: int|
                    0 <= idx < total_masks as int
                        ==> (#[trigger] dp@[idx]) as int
                            == Self::dp(
                                cost_deep,
                                m_int,
                                n_int,
                                row as int,
                                idx as u32,
                                0,
                            ),
                forall|idx: int|
                    0 <= idx < total_masks as int
                        ==> 0 <= #[trigger] dp@[idx] <= 100_000,
            decreases row,
        {
            row = row - 1;

            let mut new_dp: Vec<i32> = Vec::new();
            let mut mask: usize = 0;
            while mask < total_masks
                invariant
                    0 <= mask <= total_masks,
                    total_masks == 1usize << n,
                    total_masks <= 4096,
                    total_masks >= 2,
                    1 <= n <= 12,
                    1 <= m <= 12,
                    0 <= row < m,
                    m == cost.len(),
                    n == cost[0]@.len(),
                    dp.len() == total_masks,
                    new_dp.len() == mask,
                    cost_deep == Seq::new(cost.len() as nat, |i: int| cost@[i]@),
                    m_int == m as int,
                    n_int == n as int,
                    forall|i: int|
                        0 <= i < cost.len()
                            ==> (#[trigger] cost[i])@.len() == cost[0]@.len(),
                    forall|i: int, j: int|
                        #![trigger cost[i]@[j]]
                        0 <= i < cost.len() && 0 <= j < cost[0]@.len()
                            ==> 0 <= cost[i]@[j] <= 100,
                    forall|r: int, c: int|
                        #![trigger cost_deep[r][c]]
                        0 <= r < m_int && 0 <= c < n_int ==> 0 <= cost_deep[r][c] <= 100,
                    forall|r: int|
                        0 <= r < m_int
                            ==> (#[trigger] cost_deep[r]).len() == n_int,
                    forall|idx: int|
                        0 <= idx < total_masks as int
                            ==> (#[trigger] dp@[idx]) as int
                                == Self::dp(
                                    cost_deep,
                                    m_int,
                                    n_int,
                                    (row + 1) as int,
                                    idx as u32,
                                    0,
                                ),
                    forall|idx: int|
                        0 <= idx < total_masks as int
                            ==> 0 <= #[trigger] dp@[idx] <= 100_000,
                    forall|idx: int|
                        0 <= idx < mask as int
                            ==> (#[trigger] new_dp@[idx]) as int
                                == Self::dp(
                                    cost_deep,
                                    m_int,
                                    n_int,
                                    row as int,
                                    idx as u32,
                                    0,
                                ),
                    forall|idx: int|
                        0 <= idx < mask as int
                            ==> 0 <= #[trigger] new_dp@[idx] <= 100_000,
                decreases total_masks - mask,
            {
                let mut best: i32 = 100_000;
                let mut j: usize = 0;

                proof {
                    Self::lemma_dp_bounded(
                        cost_deep,
                        m_int,
                        n_int,
                        row as int,
                        mask as u32,
                        0,
                    );
                }

                while j < n
                    invariant
                        0 <= j <= n,
                        1 <= n <= 12,
                        1 <= m <= 12,
                        0 <= row < m,
                        0 <= mask < total_masks,
                        total_masks == 1usize << n,
                        total_masks <= 4096,
                        m == cost.len(),
                        n == cost[0]@.len(),
                        dp.len() == total_masks,
                        cost_deep == Seq::new(cost.len() as nat, |i: int| cost@[i]@),
                        m_int == m as int,
                        n_int == n as int,
                        forall|i: int|
                            0 <= i < cost.len()
                                ==> (#[trigger] cost[i])@.len() == cost[0]@.len(),
                        forall|i: int, jj: int|
                            #![trigger cost[i]@[jj]]
                            0 <= i < cost.len() && 0 <= jj < cost[0]@.len()
                                ==> 0 <= cost[i]@[jj] <= 100,
                        forall|r: int, c: int|
                            #![trigger cost_deep[r][c]]
                            0 <= r < m_int && 0 <= c < n_int
                                ==> 0 <= cost_deep[r][c] <= 100,
                        forall|r: int|
                            0 <= r < m_int
                                ==> (#[trigger] cost_deep[r]).len() == n_int,
                        forall|idx: int|
                            0 <= idx < total_masks as int
                                ==> (#[trigger] dp@[idx]) as int
                                    == Self::dp(
                                        cost_deep,
                                        m_int,
                                        n_int,
                                        (row + 1) as int,
                                        idx as u32,
                                        0,
                                    ),
                        forall|idx: int|
                            0 <= idx < total_masks as int
                                ==> 0 <= #[trigger] dp@[idx] <= 100_000,
                        0 <= best <= 100_000,
                        Self::min2(best as int, Self::dp(
                            cost_deep,
                            m_int,
                            n_int,
                            row as int,
                            mask as u32,
                            j as int,
                        )) == Self::dp(
                            cost_deep,
                            m_int,
                            n_int,
                            row as int,
                            mask as u32,
                            0,
                        ),
                    decreases n - j,
                {
                    let new_mask: usize = mask | (1usize << j);

                    proof {
                        assert(new_mask < total_masks) by (bit_vector)
                            requires
                                new_mask == mask | (1usize << j),
                                0usize <= mask < total_masks,
                                total_masks == 1usize << n,
                                0usize <= j < n,
                                1usize <= n <= 12usize,
                        ;

                        assert(new_mask as u32 == (mask as u32 | (1u32 << (j as u32))))
                            by (bit_vector)
                            requires
                                new_mask == mask | (1usize << j),
                                0usize <= mask < 4096usize,
                                0usize <= j < 12usize,
                        ;

                        assert(cost_deep[row as int][j as int] == cost[row as int]@[j as int]);
                    }

                    let val: i32 = cost[row][j] + dp[new_mask];

                    proof {
                        let dp_next = Self::dp(
                            cost_deep,
                            m_int,
                            n_int,
                            (row + 1) as int,
                            new_mask as u32,
                            0,
                        );
                        assert(dp@[new_mask as int] as int == dp_next);

                        let connect_j = cost_deep[row as int][j as int] as int + dp_next;
                        let skip_j = Self::dp(
                            cost_deep,
                            m_int,
                            n_int,
                            row as int,
                            mask as u32,
                            (j + 1) as int,
                        );
                        assert(Self::dp(
                            cost_deep,
                            m_int,
                            n_int,
                            row as int,
                            mask as u32,
                            j as int,
                        ) == Self::min2(connect_j, skip_j));

                        assert(val as int == connect_j);

                        Self::lemma_min2_assoc(best as int, connect_j, skip_j);
                    }

                    if val < best {
                        best = val;
                    }
                    j = j + 1;
                }

                proof {
                    assert(Self::dp(
                        cost_deep,
                        m_int,
                        n_int,
                        row as int,
                        mask as u32,
                        n_int,
                    ) == 100_000int);
                    assert(Self::min2(best as int, 100_000int) == best as int);
                    assert(best as int == Self::dp(
                        cost_deep,
                        m_int,
                        n_int,
                        row as int,
                        mask as u32,
                        0,
                    ));
                }

                new_dp.push(best);
                mask = mask + 1;
            }

            dp = new_dp;
        }

        proof {
            assert(dp@[0int] as int == Self::dp(cost_deep, m_int, n_int, 0, 0u32, 0));
        }

        dp[0]
    }
}

} 
