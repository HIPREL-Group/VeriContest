use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn rank_of(pref_row: Seq<i32>, u: i32) -> int
        decreases pref_row.len()
    {
        if pref_row.len() == 0 {
            0
        } else if pref_row[0] == u {
            0
        } else {
            1 + Self::rank_of(pref_row.subrange(1, pref_row.len() as int), u)
        }
    }

    pub open spec fn partner_of(x: int, pairs: Seq<Vec<i32>>) -> int
        decreases pairs.len()
    {
        if pairs.len() == 0 {
            -1
        } else if pairs.last()[0] as int == x {
            pairs.last()[1] as int
        } else if pairs.last()[1] as int == x {
            pairs.last()[0] as int
        } else {
            Self::partner_of(x, pairs.drop_last())
        }
    }

    pub open spec fn is_unhappy(x: int, n: int, preferences: Seq<Vec<i32>>, pairs: Seq<Vec<i32>>) -> bool {
        exists |u: int| 0 <= u < n && u != x
            && Self::rank_of(preferences[x]@, u as i32) < Self::rank_of(preferences[x]@, Self::partner_of(x, pairs) as i32)
            && Self::rank_of(preferences[u]@, x as i32) < Self::rank_of(preferences[u]@, Self::partner_of(u, pairs) as i32)
    }

    pub open spec fn count_unhappy(k: int, n: int, preferences: Seq<Vec<i32>>, pairs: Seq<Vec<i32>>) -> int
        decreases k
    {
        if k <= 0 {
            0
        } else {
            Self::count_unhappy(k - 1, n, preferences, pairs) +
                if Self::is_unhappy(k - 1, n, preferences, pairs) { 1int } else { 0int }
        }
    }

    pub open spec fn is_unhappy_raw(x: int, n: int, rank_view: Seq<i32>, partner_view: Seq<i32>) -> bool {
        exists |u: int| 0 <= u < n && u != x
            && rank_view[(x * n + u) as int] < rank_view[(x * n + partner_view[x] as int) as int]
            && rank_view[(u * n + x) as int] < rank_view[(u * n + partner_view[u] as int) as int]
    }

    pub open spec fn count_unhappy_raw(k: int, n: int, rank_view: Seq<i32>, partner_view: Seq<i32>) -> int
        decreases k
    {
        if k <= 0 {
            0
        } else {
            Self::count_unhappy_raw(k - 1, n, rank_view, partner_view) +
                if Self::is_unhappy_raw(k - 1, n, rank_view, partner_view) { 1int } else { 0int }
        }
    }

    proof fn rank_of_at_index(s: Seq<i32>, j: int, u: i32)
        requires
            0 <= j < s.len(),
            s[j] == u,
            forall |j1: int, j2: int| 0 <= j1 < j2 < s.len() ==> s[j1] != s[j2],
        ensures
            Self::rank_of(s, u) == j,
        decreases j,
    {
        if j == 0 {
        } else {
            let sub = s.subrange(1, s.len() as int);
            assert(sub[j - 1] == u);
            assert forall |j1: int, j2: int| 0 <= j1 < j2 < sub.len() implies sub[j1] != sub[j2] by {
                assert(sub[j1] == s[j1 + 1]);
                assert(sub[j2] == s[j2 + 1]);
            };
            Self::rank_of_at_index(sub, j - 1, u);
        }
    }

    proof fn partner_of_at_index(x: int, pairs: Seq<Vec<i32>>, ki: int)
        requires
            0 <= ki < pairs.len(),
            forall |k: int| 0 <= k < pairs.len() ==> (#[trigger] pairs[k])@.len() >= 2,
            pairs[ki][0] as int == x || pairs[ki][1] as int == x,
            forall |k1: int, k2: int| 0 <= k1 < k2 < pairs.len() ==>
                (#[trigger] pairs[k1])[0] != (#[trigger] pairs[k2])[0]
                && pairs[k1][0] != pairs[k2][1]
                && pairs[k1][1] != pairs[k2][0]
                && pairs[k1][1] != pairs[k2][1],
        ensures
            Self::partner_of(x, pairs) ==
                if pairs[ki][0] as int == x { pairs[ki][1] as int } else { pairs[ki][0] as int },
        decreases pairs.len(),
    {
        if ki == pairs.len() - 1 {
        } else {
            let last_idx = (pairs.len() - 1) as int;
            assert(pairs[last_idx] == pairs.last());
            assert(pairs.last()[0] as int != x && pairs.last()[1] as int != x) by {
                if pairs[ki][0] as int == x {
                    assert(pairs[ki][0] != pairs[last_idx][0]);
                    assert(pairs[ki][0] != pairs[last_idx][1]);
                } else {
                    assert(pairs[ki][1] != pairs[last_idx][0]);
                    assert(pairs[ki][1] != pairs[last_idx][1]);
                }
            };
            let shorter = pairs.drop_last();
            assert forall |k: int| 0 <= k < shorter.len() implies (#[trigger] shorter[k])@.len() >= 2 by {
                assert(shorter[k] == pairs[k]);
            };
            assert forall |k1: int, k2: int| 0 <= k1 < k2 < shorter.len() implies
                (#[trigger] shorter[k1])[0] != (#[trigger] shorter[k2])[0]
                && shorter[k1][0] != shorter[k2][1]
                && shorter[k1][1] != shorter[k2][0]
                && shorter[k1][1] != shorter[k2][1]
            by {
                assert(shorter[k1] == pairs[k1]);
                assert(shorter[k2] == pairs[k2]);
            };
            assert(shorter[ki] == pairs[ki]);
            Self::partner_of_at_index(x, shorter, ki);
        }
    }

    proof fn is_unhappy_equiv(
        x: int,
        n: int,
        pref: Seq<Vec<i32>>,
        pairs: Seq<Vec<i32>>,
        rank_view: Seq<i32>,
        partner_view: Seq<i32>,
    )
        requires
            0 <= x < n,
            2 <= n <= 500,
            n * n <= 250000,
            rank_view.len() == n * n,
            partner_view.len() == n,
            pref.len() == n,
            forall |x_: int, u_: int| 0 <= x_ < n && 0 <= u_ < n && u_ != x_ ==>
                #[trigger] rank_view[(x_ * n + u_) as int] as int == Self::rank_of(pref[x_]@, u_ as i32),
            forall |x_: int| 0 <= x_ < n ==>
                #[trigger] partner_view[x_] as int == Self::partner_of(x_, pairs),
            forall |x_: int| 0 <= x_ < n ==>
                0 <= partner_view[x_] <= n - 1 && partner_view[x_] as int != x_,
        ensures
            Self::is_unhappy_raw(x, n, rank_view, partner_view) == Self::is_unhappy(x, n, pref, pairs),
    {
        let px = partner_view[x] as int;
        assert(px == Self::partner_of(x, pairs));
        assert(0 <= px < n && px != x);

        assert forall |u: int| 0 <= u < n && u != x implies
            (rank_view[(x * n + u) as int] < rank_view[(x * n + px) as int]
             && rank_view[(u * n + x) as int] < rank_view[(u * n + partner_view[u] as int) as int])
            ==
            (Self::rank_of(pref[x]@, u as i32) < Self::rank_of(pref[x]@, Self::partner_of(x, pairs) as i32)
             && Self::rank_of(pref[u]@, x as i32) < Self::rank_of(pref[u]@, Self::partner_of(u, pairs) as i32))
        by {
            let pu = partner_view[u] as int;
            assert(pu == Self::partner_of(u, pairs));
            assert(0 <= pu < n && pu != u);
            assert(rank_view[(x * n + u) as int] as int == Self::rank_of(pref[x]@, u as i32));
            assert(rank_view[(x * n + px) as int] as int == Self::rank_of(pref[x]@, px as i32));
            assert(rank_view[(u * n + x) as int] as int == Self::rank_of(pref[u]@, x as i32));
            assert(rank_view[(u * n + pu) as int] as int == Self::rank_of(pref[u]@, pu as i32));
        };
    }

    proof fn count_unhappy_equiv(
        k: int,
        n: int,
        pref: Seq<Vec<i32>>,
        pairs: Seq<Vec<i32>>,
        rank_view: Seq<i32>,
        partner_view: Seq<i32>,
    )
        requires
            0 <= k <= n,
            2 <= n <= 500,
            n * n <= 250000,
            rank_view.len() == n * n,
            partner_view.len() == n,
            pref.len() == n,
            forall |x_: int, u_: int| 0 <= x_ < n && 0 <= u_ < n && u_ != x_ ==>
                #[trigger] rank_view[(x_ * n + u_) as int] as int == Self::rank_of(pref[x_]@, u_ as i32),
            forall |x_: int| 0 <= x_ < n ==>
                #[trigger] partner_view[x_] as int == Self::partner_of(x_, pairs),
            forall |x_: int| 0 <= x_ < n ==>
                0 <= partner_view[x_] <= n - 1 && partner_view[x_] as int != x_,
        ensures
            Self::count_unhappy_raw(k, n, rank_view, partner_view) == Self::count_unhappy(k, n, pref, pairs),
        decreases k,
    {
        if k > 0 {
            Self::count_unhappy_equiv(k - 1, n, pref, pairs, rank_view, partner_view);
            Self::is_unhappy_equiv(k - 1, n, pref, pairs, rank_view, partner_view);
        }
    }

    pub fn unhappy_friends(n: i32, preferences: Vec<Vec<i32>>, pairs: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= n <= 500,
            n % 2 == 0,
            preferences.len() == n,
            forall |i: int| 0 <= i < n ==> (#[trigger] preferences[i]).len() == n - 1,
            forall |i: int, j: int| 0 <= i < n && 0 <= j < n - 1 ==>
                0 <= #[trigger] preferences[i][j] <= n - 1,
            forall |i: int, j: int| 0 <= i < n && 0 <= j < n - 1 ==>
                preferences[i][j] != i as i32,
            forall |i: int, j1: int, j2: int| 0 <= i < n && 0 <= j1 < n - 1 && 0 <= j2 < n - 1 && j1 != j2 ==>
                #[trigger] preferences[i][j1] != #[trigger] preferences[i][j2],
            forall |i: int, u: int| #![trigger preferences[i], preferences[u]]
                0 <= i < n && 0 <= u < n && u != i ==>
                exists |j: int| 0 <= j < n - 1 && preferences[i][j] == u as i32,
            pairs.len() == n / 2,
            forall |k: int| 0 <= k < n / 2 ==>
                (#[trigger] pairs[k]).len() == 2
                && 0 <= pairs[k][0] <= n - 1
                && 0 <= pairs[k][1] <= n - 1
                && pairs[k][0] != pairs[k][1],
            forall |k1: int, k2: int| 0 <= k1 < k2 < n / 2 ==>
                (#[trigger] pairs[k1])[0] != (#[trigger] pairs[k2])[0]
                && pairs[k1][0] != pairs[k2][1]
                && pairs[k1][1] != pairs[k2][0]
                && pairs[k1][1] != pairs[k2][1],
            forall |x: int| #![trigger preferences[x]]
                0 <= x < n ==>
                exists |k: int| 0 <= k < n / 2 && (pairs[k][0] as int == x || pairs[k][1] as int == x),
        ensures
            0 <= result <= n,
            result as int == Self::count_unhappy(n as int, n as int, preferences@, pairs@),
    {
        proof {
            assert(n as int * n as int <= 250000) by (nonlinear_arith)
                requires 2 <= n as int <= 500;
        }

        let mut rank: Vec<i32> = Vec::new();
        let mut idx = 0;
        while idx < n * n
            invariant
                0 <= idx <= n * n,
                n * n <= 250000,
                rank.len() == idx as nat,
                forall |m: int| 0 <= m < idx ==> rank[m] == 0i32,
            decreases n * n - idx,
        {
            rank.push(0);
            idx = idx + 1;
        }
        let mut i = 0;
        while i < n
            invariant
                0 <= i <= n,
                2 <= n <= 500,
                n * n <= 250000,
                rank.len() == (n * n) as nat,
                preferences.len() == n,
                forall |ii: int| 0 <= ii < n ==> (#[trigger] preferences[ii]).len() == n - 1,
                forall |ii: int, jj: int| 0 <= ii < n && 0 <= jj < n - 1 ==>
                    0 <= #[trigger] preferences[ii][jj] <= n - 1,
                forall |ii: int, jj: int| 0 <= ii < n && 0 <= jj < n - 1 ==>
                    preferences[ii][jj] != ii as i32,
                forall |ii: int, j1: int, j2: int| 0 <= ii < n && 0 <= j1 < n - 1 && 0 <= j2 < n - 1 && j1 != j2 ==>
                    #[trigger] preferences[ii][j1] != #[trigger] preferences[ii][j2],
                forall |x: int, jj: int| 0 <= x < i && 0 <= jj < n - 1 ==>
                    (x * n + preferences[x][jj]) >= 0 && (x * n + preferences[x][jj]) < (n * n)
                    && #[trigger] rank[(x * n + preferences[x][jj]) as int] == jj as i32,
            decreases n - i,
        {
            let mut j = 0;

            proof {
                assert forall |x: int, jj_: int| 0 <= x < i && 0 <= jj_ < n - 1 implies
                    (x * n + preferences[x][jj_]) >= 0 && (x * n + preferences[x][jj_]) < (n * n)
                    && rank[(x * n + preferences[x][jj_]) as int] == jj_ as i32
                by {
                    assert(0 <= preferences[x][jj_] && preferences[x][jj_] <= n - 1);
                    assert(x * n + preferences[x][jj_] >= 0) by (nonlinear_arith)
                        requires 0 <= x, 0 <= n as int, 0 <= preferences[x][jj_] as int;
                    assert(x * n + preferences[x][jj_] < n * n) by (nonlinear_arith)
                        requires 0 <= x, x < n as int, preferences[x][jj_] as int <= n as int - 1, 2 <= n as int;
                };
            }

            while j < n - 1
                invariant
                    0 <= i < n,
                    0 <= j <= n - 1,
                    2 <= n <= 500,
                    n * n <= 250000,
                    rank.len() == (n * n) as nat,
                    preferences.len() == n,
                    forall |ii: int| 0 <= ii < n ==> (#[trigger] preferences[ii]).len() == n - 1,
                    forall |ii: int, jj: int| 0 <= ii < n && 0 <= jj < n - 1 ==>
                        0 <= #[trigger] preferences[ii][jj] <= n - 1,
                    forall |ii: int, jj: int| 0 <= ii < n && 0 <= jj < n - 1 ==>
                        preferences[ii][jj] != ii as i32,
                    forall |ii: int, j1: int, j2: int| 0 <= ii < n && 0 <= j1 < n - 1 && 0 <= j2 < n - 1 && j1 != j2 ==>
                        #[trigger] preferences[ii][j1] != #[trigger] preferences[ii][j2],
                    forall |x: int, jj: int| 0 <= x < i && 0 <= jj < n - 1 ==>
                        (x * n + preferences[x][jj]) >= 0 && (x * n + preferences[x][jj]) < (n * n)
                        && #[trigger] rank[(x * n + preferences[x][jj]) as int] == jj as i32,
                    forall |jj: int| 0 <= jj < j ==>
                        (i * n + preferences[i as int][jj]) >= 0 && (i * n + preferences[i as int][jj]) < (n * n)
                        && #[trigger] rank[(i * n + preferences[i as int][jj]) as int] == jj as i32,
                decreases n - 1 - j,
            {
                let p = preferences[i as usize][j as usize];

                proof {
                    assert(0 <= p <= n - 1);
                    assert(0 <= i * n + p < n * n) by (nonlinear_arith)
                        requires 0 <= i < n, 0 <= p < n, 2 <= n <= 500;
                }

                rank.set((i * n + p) as usize, j);

                proof {
                    
                    assert forall |x: int, jj2: int| 0 <= x < i && 0 <= jj2 < n - 1 implies
                        (x * n + preferences[x][jj2]) >= 0 && (x * n + preferences[x][jj2]) < (n * n)
                        && rank[(x * n + preferences[x][jj2]) as int] == jj2 as i32
                    by {
                        assert(0 <= preferences[x][jj2] && preferences[x][jj2] <= n - 1);
                        assert(x * n + preferences[x][jj2] >= 0) by (nonlinear_arith)
                            requires 0 <= x, 0 <= n as int, 0 <= preferences[x][jj2] as int;
                        assert(x * n + preferences[x][jj2] < n * n) by (nonlinear_arith)
                            requires 0 <= x, x < n as int, preferences[x][jj2] as int <= n as int - 1, 2 <= n as int;
                        assert(x * n + preferences[x][jj2] < i * n) by (nonlinear_arith)
                            requires 0 <= x, x + 1 <= i as int, preferences[x][jj2] as int <= n as int - 1, 2 <= n as int;
                    };
                    
                    assert forall |jj2: int| 0 <= jj2 < j implies
                        (i * n + preferences[i as int][jj2]) >= 0 && (i * n + preferences[i as int][jj2]) < (n * n)
                        && rank[(i * n + preferences[i as int][jj2]) as int] == jj2 as i32
                    by {
                        assert(0 <= preferences[i as int][jj2] && preferences[i as int][jj2] <= n - 1);
                        assert(i * n + preferences[i as int][jj2] >= 0) by (nonlinear_arith)
                            requires 0 <= i as int, 0 <= n as int, 0 <= preferences[i as int][jj2] as int;
                        assert(i * n + preferences[i as int][jj2] < n * n) by (nonlinear_arith)
                            requires 0 <= i < n, preferences[i as int][jj2] as int <= n as int - 1, 2 <= n as int;
                        assert(preferences[i as int][jj2] != preferences[i as int][j as int]);
                    };
                }

                j = j + 1;
            }

            proof {
                
                assert forall |x: int, jj: int| 0 <= x <= i && 0 <= jj < n - 1 implies
                    (x * n + preferences[x][jj]) >= 0 && (x * n + preferences[x][jj]) < (n * n)
                    && rank[(x * n + preferences[x][jj]) as int] == jj as i32
                by {
                    assert(0 <= preferences[x][jj] && preferences[x][jj] <= n - 1);
                    assert(x * n + preferences[x][jj] >= 0) by (nonlinear_arith)
                        requires 0 <= x, 0 <= n as int, 0 <= preferences[x][jj] as int;
                    assert(x * n + preferences[x][jj] < n * n) by (nonlinear_arith)
                        requires 0 <= x, x < n as int, preferences[x][jj] as int <= n as int - 1, 2 <= n as int;
                    if x < i as int {
                    } else {
                    }
                };
            }

            i = i + 1;
        }

        proof {
            assert forall |x: int, u: int| 0 <= x < n && 0 <= u < n && u != x implies
                0 <= (x * n + u) && (x * n + u) < n * n
                && #[trigger] rank[(x * n + u) as int] as int == Self::rank_of(preferences[x]@, u as i32)
            by {
                assert(0 <= x * n + u) by (nonlinear_arith)
                    requires 0 <= x, 0 <= n as int, 0 <= u;
                assert(x * n + u < n * n) by (nonlinear_arith)
                    requires 0 <= x, x < n as int, 0 <= u, u < n as int, 2 <= n as int;
                assert(preferences[x].len() == n - 1);
                assert(preferences[u].len() == n - 1);
                let jj = choose |jj: int| 0 <= jj < n - 1 && preferences[x][jj] == u as i32;
                assert((x * n + preferences[x][jj]) >= 0 && (x * n + preferences[x][jj]) < (n * n)) by (nonlinear_arith)
                    requires 0 <= x < n, 0 <= preferences[x][jj] < n, 2 <= n <= 500;
                assert(rank[(x * n + preferences[x][jj]) as int] == jj as i32);
                assert(preferences[x][jj] == u as i32);
                assert(x * n + preferences[x][jj] == x * n + u) by {
                    assert(preferences[x][jj] as int == u as int);
                };
                assert(rank[(x * n + u) as int] == jj as i32);
                assert(preferences[x]@[jj] == u as i32) by {
                    assert(preferences[x]@[jj] == preferences[x][jj]);
                };
                assert forall |j1: int, j2: int| 0 <= j1 < j2 < preferences[x]@.len() implies
                    preferences[x]@[j1] != preferences[x]@[j2]
                by {
                    assert(preferences[x]@[j1] == preferences[x][j1]);
                    assert(preferences[x]@[j2] == preferences[x][j2]);
                };
                Self::rank_of_at_index(preferences[x]@, jj, u as i32);
            };
        }

        let mut partner: Vec<i32> = Vec::new();
        idx = 0;
        while idx < n
            invariant
                0 <= idx <= n,
                2 <= n <= 500,
                partner.len() == idx as nat,
                forall |m: int| 0 <= m < idx ==> partner[m] == 0i32,
            decreases n - idx,
        {
            partner.push(0);
            idx = idx + 1;
        }
        let mut k = 0;
        while k < n / 2
            invariant
                0 <= k <= n / 2,
                2 <= n <= 500,
                n % 2 == 0,
                partner.len() == n as nat,
                pairs.len() == n / 2,
                forall |kk: int| 0 <= kk < n / 2 ==>
                    (#[trigger] pairs[kk]).len() == 2
                    && 0 <= pairs[kk][0] <= n - 1
                    && 0 <= pairs[kk][1] <= n - 1
                    && pairs[kk][0] != pairs[kk][1],
                forall |k1: int, k2: int| 0 <= k1 < k2 < n / 2 ==>
                    (#[trigger] pairs[k1])[0] != (#[trigger] pairs[k2])[0]
                    && pairs[k1][0] != pairs[k2][1]
                    && pairs[k1][1] != pairs[k2][0]
                    && pairs[k1][1] != pairs[k2][1],
                forall |kk: int| 0 <= kk < k ==>
                    partner[pairs[kk][0] as int] == pairs[kk][1]
                    && #[trigger] partner[pairs[kk][1] as int] == pairs[kk][0],
            decreases n / 2 - k,
        {
            let a = pairs[k as usize][0];
            let b = pairs[k as usize][1];

            let ghost old_partner = partner@;

            
            proof {
                assert forall |kk: int| 0 <= kk < k implies
                    old_partner[pairs[kk][0] as int] == pairs[kk][1]
                    && old_partner[pairs[kk][1] as int] == pairs[kk][0]
                by {
                    
                    assert(partner[pairs[kk][1] as int] == pairs[kk][0]);
                };
            }

            partner.set(a as usize, b);

            let ghost after_first = partner@;

            partner.set(b as usize, a);

            proof {
                assert(a != b);
                assert(partner[a as int] == after_first[a as int]) by {
                    assert(a as int != b as int);
                };
                assert(after_first[a as int] == b);
                assert(partner[a as int] == b);
                assert(partner[b as int] == a);

                assert forall |kk: int| 0 <= kk < k + 1 implies
                    partner[pairs[kk][0] as int] == pairs[kk][1]
                    && #[trigger] partner[pairs[kk][1] as int] == pairs[kk][0]
                by {
                    if kk < k {
                        assert(pairs[kk][0] != pairs[k as int][0]);
                        assert(pairs[kk][0] != pairs[k as int][1]);
                        assert(pairs[kk][1] != pairs[k as int][0]);
                        assert(pairs[kk][1] != pairs[k as int][1]);
                        assert(partner[pairs[kk][0] as int] == after_first[pairs[kk][0] as int]) by {
                            assert(pairs[kk][0] as int != b as int);
                        };
                        assert(after_first[pairs[kk][0] as int] == old_partner[pairs[kk][0] as int]) by {
                            assert(pairs[kk][0] as int != a as int);
                        };
                        assert(partner[pairs[kk][1] as int] == after_first[pairs[kk][1] as int]) by {
                            assert(pairs[kk][1] as int != b as int);
                        };
                        assert(after_first[pairs[kk][1] as int] == old_partner[pairs[kk][1] as int]) by {
                            assert(pairs[kk][1] as int != a as int);
                        };
                    }
                };
            }

            k = k + 1;
        }

        proof {
            assert forall |x: int| 0 <= x < n implies
                #[trigger] partner[x] as int == Self::partner_of(x, pairs@)
            by {
                assert(preferences[x].len() == n - 1);
                let ki = choose |ki: int| 0 <= ki < n / 2 && (pairs[ki][0] as int == x || pairs[ki][1] as int == x);
                assert(partner[pairs[ki][1] as int] == pairs[ki][0]);
                assert(partner[pairs[ki][0] as int] == pairs[ki][1]);
                if pairs[ki][0] as int == x {
                    assert(partner[x] == pairs[ki][1]);
                } else {
                    assert(partner[x] == pairs[ki][0]);
                }
                Self::partner_of_at_index(x, pairs@, ki);
            };
        }

        proof {
            assert forall |x: int| 0 <= x < n implies
                0 <= partner[x] <= n - 1 && partner[x] as int != x
            by {
                assert(preferences[x].len() == n - 1);
                let ki = choose |ki: int| 0 <= ki < n / 2 && (pairs[ki][0] as int == x || pairs[ki][1] as int == x);
                assert(partner[pairs[ki][1] as int] == pairs[ki][0]);
                assert(partner[pairs[ki][0] as int] == pairs[ki][1]);
                if pairs[ki][0] as int == x {
                    assert(partner[x] == pairs[ki][1]);
                } else {
                    assert(partner[x] == pairs[ki][0]);
                }
            };
        }

        let mut count = 0;
        i = 0;

        while i < n
            invariant
                0 <= i <= n,
                0 <= count <= i,
                2 <= n <= 500,
                n * n <= 250000,
                n % 2 == 0,
                rank.len() == (n * n) as nat,
                partner.len() == n as nat,
                preferences.len() == n,
                pairs.len() == n / 2,
                forall |ii: int| 0 <= ii < n ==> (#[trigger] preferences[ii]).len() == n - 1,
                forall |ii: int, jj: int| 0 <= ii < n && 0 <= jj < n - 1 ==>
                    0 <= #[trigger] preferences[ii][jj] <= n - 1,
                forall |x: int, jj: int| 0 <= x < n && 0 <= jj < n - 1 ==>
                    #[trigger] rank[(x * n + preferences[x][jj]) as int] == jj as i32,
                forall |x: int| 0 <= x < n ==>
                    0 <= partner[x] <= n - 1 && partner[x] as int != x,
                forall |x: int| 0 <= x < n ==>
                    #[trigger] partner[x] as int == Self::partner_of(x, pairs@),
                count as int == Self::count_unhappy_raw(i as int, n as int, rank@, partner@),
            decreases n - i,
        {
            let mut u = 0;
            let mut found = false;
            while u < n && !found
                invariant
                    0 <= u <= n,
                    0 <= i < n,
                    2 <= n <= 500,
                    n * n <= 250000,
                    rank.len() == (n * n) as nat,
                    partner.len() == n as nat,
                    preferences.len() == n,
                    pairs.len() == n / 2,
                    forall |ii: int| 0 <= ii < n ==> (#[trigger] preferences[ii]).len() == n - 1,
                    forall |ii: int, jj: int| 0 <= ii < n && 0 <= jj < n - 1 ==>
                        0 <= #[trigger] preferences[ii][jj] <= n - 1,
                    forall |x: int, jj: int| 0 <= x < n && 0 <= jj < n - 1 ==>
                        #[trigger] rank[(x * n + preferences[x][jj]) as int] == jj as i32,
                    forall |x: int| 0 <= x < n ==>
                        0 <= partner[x] <= n - 1 && partner[x] as int != x,
                    found ==> Self::is_unhappy_raw(i as int, n as int, rank@, partner@),
                    !found ==> forall |w: int| 0 <= w < u && w != i as int ==>
                        !(rank[(i * n + w) as int] < rank[(i * n + partner[i as int] as int) as int]
                          && rank[(w * n + i) as int] < rank[(w * n + partner[w] as int) as int]),
                decreases n - u,
            {
                if u != i {
                    proof {
                        assert(0 <= i * n + u < n * n) by (nonlinear_arith)
                            requires 0 <= i < n, 0 <= u < n, 2 <= n <= 500;
                        assert(0 <= (i * n + partner[i as int] as int) < n * n) by (nonlinear_arith)
                            requires 0 <= i < n, 0 <= partner[i as int] < n, 2 <= n <= 500;
                        assert(0 <= u * n + i < n * n) by (nonlinear_arith)
                            requires 0 <= u < n, 0 <= i < n, 2 <= n <= 500;
                        assert(0 <= (u * n + partner[u as int] as int) < n * n) by (nonlinear_arith)
                            requires 0 <= u < n, 0 <= partner[u as int] < n, 2 <= n <= 500;
                    }
                    if rank[(i * n + u) as usize] < rank[(i * n + partner[i as usize]) as usize]
                        && rank[(u * n + i) as usize] < rank[(u * n + partner[u as usize]) as usize]
                    {
                        found = true;
                        proof {
                            
                            assert(Self::is_unhappy_raw(i as int, n as int, rank@, partner@));
                        }
                    }
                }
                u = u + 1;
            }

            proof {
                if found {
                } else {
                    assert forall |w: int| 0 <= w < n && w != i as int implies
                        !(rank[(i * n + w) as int] < rank[(i * n + partner[i as int] as int) as int]
                          && rank[(w * n + i) as int] < rank[(w * n + partner[w] as int) as int])
                    by {};
                    assert(!Self::is_unhappy_raw(i as int, n as int, rank@, partner@));
                }
            }

            if found {
                count = count + 1;
            }
            i = i + 1;
        }

        proof {
            
            assert forall |x: int, u: int| 0 <= x < n && 0 <= u < n && u != x implies
                #[trigger] rank[(x * n + u) as int] as int == Self::rank_of(preferences[x]@, u as i32)
            by {
                assert(0 <= x * n + u) by (nonlinear_arith)
                    requires 0 <= x, 0 <= n as int, 0 <= u;
                assert(x * n + u < n * n) by (nonlinear_arith)
                    requires 0 <= x, x < n as int, 0 <= u, u < n as int, 2 <= n as int;
                assert(preferences[x].len() == n - 1);
                assert(preferences[u].len() == n - 1);
                let jj = choose |jj: int| 0 <= jj < n - 1 && preferences[x][jj] == u as i32;
                assert((x * n + preferences[x][jj]) >= 0 && (x * n + preferences[x][jj]) < (n * n)) by (nonlinear_arith)
                    requires 0 <= x < n, 0 <= preferences[x][jj] < n, 2 <= n <= 500;
                assert(rank[(x * n + preferences[x][jj]) as int] == jj as i32);
                assert(preferences[x][jj] == u as i32);
                assert(x * n + preferences[x][jj] == x * n + u) by {
                    assert(preferences[x][jj] as int == u as int);
                };
                assert(rank[(x * n + u) as int] == jj as i32);
                assert(preferences[x]@[jj] == u as i32) by {
                    assert(preferences[x]@[jj] == preferences[x][jj]);
                };
                assert forall |j1: int, j2: int| 0 <= j1 < j2 < preferences[x]@.len() implies
                    preferences[x]@[j1] != preferences[x]@[j2]
                by {
                    assert(preferences[x]@[j1] == preferences[x][j1]);
                    assert(preferences[x]@[j2] == preferences[x][j2]);
                };
                Self::rank_of_at_index(preferences[x]@, jj, u as i32);
            };
            Self::count_unhappy_equiv(n as int, n as int, preferences@, pairs@, rank@, partner@);
        }

        count
    }
}

}
