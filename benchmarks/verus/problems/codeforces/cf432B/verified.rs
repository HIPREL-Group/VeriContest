use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_home_prefix(home: Seq<i32>, k: int, color: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        count_home_prefix(home, k - 1, color) + if home[k - 1] == color { 1int } else { 0int }
    }
}

proof fn lemma_count_home_prefix_zero(home: Seq<i32>, color: int)
    ensures
        count_home_prefix(home, 0, color) == 0,
{
    reveal_with_fuel(count_home_prefix, 1);
}

proof fn lemma_count_home_prefix_at_color(home: Seq<i32>, k: int, color: int)
    requires
        0 <= k < home.len(),
    ensures
        count_home_prefix(home, k + 1, color) == count_home_prefix(home, k, color)
            + if home[k] == color { 1int } else { 0int },
{
    reveal_with_fuel(count_home_prefix, 2);
}

proof fn lemma_count_home_prefix_nonneg(home: Seq<i32>, k: int, color: int)
    requires
        0 <= k <= home.len(),
    ensures
        0 <= count_home_prefix(home, k, color),
    decreases k,
{
    if k > 0 {
        lemma_count_home_prefix_nonneg(home, k - 1, color);
        lemma_count_home_prefix_at_color(home, k - 1, color);
    } else {
        lemma_count_home_prefix_zero(home, color);
    }
}

proof fn lemma_count_home_prefix_le_k(home: Seq<i32>, k: int, color: int)
    requires
        0 <= k <= home.len(),
    ensures
        count_home_prefix(home, k, color) <= k,
    decreases k,
{
    if k > 0 {
        lemma_count_home_prefix_le_k(home, k - 1, color);
        lemma_count_home_prefix_at_color(home, k - 1, color);
    } else {
        lemma_count_home_prefix_zero(home, color);
    }
}

proof fn lemma_count_prefix_eq_n_implies_all_homes_match(
    home: Seq<i32>,
    n: int,
    color: int,
)
    requires
        0 <= n <= home.len(),
        count_home_prefix(home, n, color) == n,
    ensures
        forall|j: int| 0 <= j < n ==> #[trigger] home[j] == color,
    decreases n,
{
    if n == 0 {
    } else {
        lemma_count_home_prefix_at_color(home, n - 1, color);
        lemma_count_home_prefix_le_k(home, n - 1, color);
        assert(count_home_prefix(home, n, color)
            == count_home_prefix(home, n - 1, color) + if home[n - 1] == color { 1int } else { 0int });
        assert(count_home_prefix(home, n - 1, color) <= n - 1);
        assert(count_home_prefix(home, n, color) == n);
        assert(count_home_prefix(home, n - 1, color) == n - 1);
        assert(if home[n - 1] == color { 1int } else { 0int } == 1);
        assert(home[n - 1] == color);
        lemma_count_prefix_eq_n_implies_all_homes_match(home, n - 1, color);
    }
}

proof fn lemma_count_excludes_self(
    home: Seq<i32>,
    away: Seq<i32>,
    idx: int,
)
    requires
        home.len() == away.len(),
        forall|i: int| 0 <= i < home.len() ==> #[trigger] home[i] != away[i],
        0 <= idx < home.len(),
    ensures
        count_home_prefix(home, home.len() as int, away[idx] as int) <= home.len() as int - 1,
{
    let n = home.len() as int;
    let color = away[idx] as int;
    assert(home[idx] != color);
    lemma_count_home_prefix_le_k(home, n, color);
    assert(count_home_prefix(home, n, color) <= n);
    assert(count_home_prefix(home, n, color) <= n - 1) by {
        if count_home_prefix(home, n, color) == n {
            lemma_count_prefix_eq_n_implies_all_homes_match(home, n, color);
            assert(home[idx] == color);
        }
    }
}

proof fn lemma_freq_matches_after_update(
    home: Seq<i32>,
    i: int,
    oldf: Seq<i32>,
    newf: Seq<i32>,
    ci: int,
    newv: i32,
)
    requires
        0 <= i < home.len(),
        ci == home[i] as int,
        1 <= ci <= 100000,
        oldf.len() == 100001,
        forall|c: int| 1 <= c <= 100000 ==> #[trigger] oldf[c] == count_home_prefix(home, i, c),
        newf == oldf.update(ci, newv),
        newv as int == oldf[ci] as int + 1,
    ensures
        forall|c: int| 1 <= c <= 100000 ==> #[trigger] newf[c] == count_home_prefix(home, i + 1, c),
{
    assert forall|c: int| 1 <= c <= 100000 implies newf[c] == count_home_prefix(home, i + 1, c) by {
        lemma_count_home_prefix_at_color(home, i, c);
        if c == ci {
            assert(newf[c] == newv);
            assert(newv as int == oldf[c] as int + 1);
            assert(oldf[c] == count_home_prefix(home, i, c));
            assert(home[i] as int == ci);
            assert(ci == c);
            assert(home[i] as int == c);
            assert(count_home_prefix(home, i + 1, c) == count_home_prefix(home, i, c) + 1int);
        } else {
            assert(newf[c] == oldf[c]);
            assert(oldf[c] == count_home_prefix(home, i, c));
            assert(home[i] as int != c);
            assert(count_home_prefix(home, i + 1, c) == count_home_prefix(home, i, c));
        }
    }
}

impl Solution {
    pub fn football_kit_games(home: Vec<i32>, away: Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
        requires
            2 <= home.len() <= 100_000,
            home.len() == away.len(),
            forall|i: int| 0 <= i < home.len() ==> 1 <= #[trigger] home[i] && home[i] <= 100_000,
            forall|i: int| 0 <= i < away.len() ==> 1 <= #[trigger] away[i] && away[i] <= 100_000,
            forall|i: int| 0 <= i < home.len() ==> #[trigger] home[i] != away[i],
        ensures
            result.0.len() == home.len(),
            result.1.len() == home.len(),
            forall|i: int| 0 <= i < home.len() ==> result.0[i] as int == (home.len() as int - 1)
                + count_home_prefix(home@, home.len() as int, away[i] as int)
                && result.1[i] as int == (home.len() as int - 1)
                    - count_home_prefix(home@, home.len() as int, away[i] as int),
    {
        let n = home.len();
        let mut freq = Vec::new();
        let mut z = 0usize;
        while z < 100001
            invariant
                z <= 100001,
                freq.len() == z,
                forall|k: int| 0 <= k < freq.len() as int ==> #[trigger] freq[k] == 0,
            decreases 100001 - z,
        {
            let ghost freq_old = freq@;
            freq.push(0i32);
            proof {
                assert(freq@ == freq_old.push(0i32));
            }
            z += 1;
        }
        proof {
            assert(freq.len() == 100001);
            assert forall|c: int| 1 <= c <= 100000 implies freq[c] == count_home_prefix(home@, 0, c) by {
                lemma_count_home_prefix_zero(home@, c);
            }
        }
        let mut i = 0usize;
        while i < n
            invariant
                n == home.len(),
                n <= 100_000,
                freq.len() == 100001,
                0 <= i <= n,
                forall|t: int| 0 <= t < home.len() ==> 1 <= #[trigger] home[t] && home[t] <= 100_000,
                forall|c: int| 1 <= c <= 100000 ==> #[trigger] freq[c] as int == count_home_prefix(home@, i as int, c),
            decreases n - i,
        {
            let ghost freq_before = freq@;
            let cidx = home[i] as usize;
            let oldv = freq[cidx];
            proof {
                let ci = home[i as int] as int;
                assert(1 <= ci <= 100000);
                lemma_count_home_prefix_nonneg(home@, i as int, ci);
                lemma_count_home_prefix_le_k(home@, i as int, ci);
                assert(oldv == count_home_prefix(home@, i as int, ci));
                assert((oldv as int) <= i as int);
                assert((i as int) < n as int);
                assert((oldv as int) + 1 <= n as int);
                assert(oldv == freq_before[ci]);
            }
            let newv = oldv + 1;
            freq.set(cidx, newv);
            proof {
                let ci = home[i as int] as int;
                assert(freq@ == freq_before.update(ci, newv));
                assert(newv as int == freq_before[ci] as int + 1);
                lemma_freq_matches_after_update(home@, i as int, freq_before, freq@, ci, newv);
            }
            i += 1;
        }
        proof {
            assert(i == n);
            assert forall|c: int| 1 <= c <= 100000 implies #[trigger] freq[c] as int == count_home_prefix(home@, n as int, c) by {}
        }
        let mut games_home_kit = Vec::new();
        let mut games_away_kit = Vec::new();
        let mut j = 0usize;
        proof {
            assert(2 <= n);
            assert(n <= 100_000);
        }
        let nn = n as i32;
        proof {
            assert(2 <= nn);
            assert(nn <= 100000);
        }
        while j < n
            invariant
                n == home.len(),
                n == away.len(),
                n <= 100_000,
                2 <= nn,
                nn <= 100000,
                nn == n as i32,
                freq.len() == 100001,
                games_home_kit.len() == j,
                games_away_kit.len() == j,
                0 <= j <= n,
                forall|t: int| 0 <= t < away.len() as int ==> 1 <= #[trigger] away[t] && away[t] <= 100_000,
                forall|t: int| 0 <= t < home.len() as int ==> #[trigger] home[t] != away[t],
                forall|c: int| 1 <= c <= 100000 ==> #[trigger] freq[c] as int == count_home_prefix(home@, n as int, c),
                forall|t: int| 0 <= t < j as int ==> games_home_kit[t] as int == (n as int - 1)
                    + count_home_prefix(home@, n as int, away[t] as int)
                    && games_away_kit[t] as int == (n as int - 1)
                        - count_home_prefix(home@, n as int, away[t] as int),
            decreases n - j,
        {
            proof {
                assert(j < n);
                assert(n == away.len());
                assert((j as int) < away.len() as int);
            }
            let aj = away[j];
            let c = aj as usize;
            let cnt = freq[c];
            proof {
                let ac = aj as int;
                assert(1 <= ac <= 100000);
                assert(freq[c as int] as int == count_home_prefix(home@, n as int, ac));
                assert(home@.len() == away@.len());
                lemma_count_excludes_self(home@, away@, j as int);
                lemma_count_home_prefix_nonneg(home@, n as int, ac);
                assert(cnt as int == count_home_prefix(home@, n as int, ac));
                assert(cnt as int >= 0);
                assert(cnt as int <= n as int - 1);
                assert((n as int - 1) - cnt as int >= 0);
                assert((n as int - 1) + cnt as int <= 200000);
                assert(cnt as int <= (nn - 1) as int);
                assert((nn - 1) + cnt <= 200000);
                assert((nn - 1) - cnt >= 0);
                assert((nn - 1) - cnt <= 100000);
                assert(games_home_kit.len() == j);
                assert(games_away_kit.len() == j);
            }
            games_home_kit.push((nn - 1) + cnt);
            games_away_kit.push((nn - 1) - cnt);
            proof {
                let ac = aj as int;
                assert(games_home_kit.len() == j + 1);
                assert(games_home_kit[j as int] as int == (n as int - 1) + count_home_prefix(home@, n as int, ac));
                assert(games_away_kit[j as int] as int == (n as int - 1) - count_home_prefix(home@, n as int, ac));
            }
            j += 1;
        }
        (games_home_kit, games_away_kit)
    }
}

}
