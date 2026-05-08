use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;



pub open spec fn is_valid_team(team: Seq<int>, scores: Seq<i32>, ages: Seq<i32>) -> bool {
    &&& forall|k: int| 0 <= k < team.len() ==> 0 <= #[trigger] team[k] < scores.len() as int
    &&& forall|k: int, l: int| 0 <= k < l < team.len() ==> team[k] != team[l]
    &&& forall|k: int, l: int| 0 <= k < team.len() && 0 <= l < team.len()
        ==> (ages[team[k]] < ages[team[l]] ==> scores[team[k]] <= scores[team[l]])
}

pub open spec fn team_score_sum(team: Seq<int>, scores: Seq<i32>) -> int
    decreases team.len(),
{
    if team.len() <= 0 {
        0
    } else {
        scores[team.last()] as int + team_score_sum(team.drop_last(), scores)
    }
}

pub open spec fn is_index_permutation(p: Seq<int>, n: int) -> bool {
    p.len() == n
        && forall|i: int| 0 <= i < n ==> 0 <= #[trigger] p[i] < n
        && forall|i: int, j: int| 0 <= i < j < n ==> p[i] != p[j]
}

pub open spec fn sorted_by_age_score(ages: Seq<i32>, scores: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < ages.len()
        ==> (ages[i] < ages[j] || (ages[i] == ages[j] && scores[i] <= scores[j]))
}

spec fn max_dp_before(ss: Seq<i32>, i: int, bound: i32) -> int
    decreases i, 0nat,
{
    if i <= 0 {
        0
    } else {
        let rest = max_dp_before(ss, i - 1, bound);
        if ss[i - 1] <= bound {
            let cur = dp_at(ss, i - 1);
            if cur > rest { cur } else { rest }
        } else {
            rest
        }
    }
}

spec fn dp_at(ss: Seq<i32>, i: int) -> int
    decreases i, 1nat,
{
    if i < 0 {
        0
    } else {
        ss[i] as int + max_dp_before(ss, i, ss[i])
    }
}

spec fn overall_best(ss: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        let prev = overall_best(ss, end - 1);
        let cur = dp_at(ss, end - 1);
        if cur > prev { cur } else { prev }
    }
}



spec fn max_inv_idx(team: Seq<int>, inv: Seq<int>) -> int
    decreases team.len(),
{
    if team.len() <= 1 {
        0
    } else {
        let prev = max_inv_idx(team.drop_last(), inv);
        if inv[team[team.len() - 1]] >= inv[team[prev]] {
            (team.len() - 1) as int
        } else {
            prev
        }
    }
}



proof fn lemma_swap_preserves_index_permutation(p: Seq<int>, i: int, j: int, n: int)
    requires
        is_index_permutation(p, n),
        0 <= i < n,
        0 <= j < n,
    ensures
        is_index_permutation(p.update(i, p[j]).update(j, p[i]), n),
{
    let q = p.update(i, p[j]).update(j, p[i]);
    assert forall|k: int| 0 <= k < n implies 0 <= #[trigger] q[k] < n by {
        if k == i { assert(q[k] == p[j]); }
        else if k == j { assert(q[k] == p[i]); }
        else { assert(q[k] == p[k]); }
    }
    assert forall|a: int, b: int| 0 <= a < b < n implies q[a] != q[b] by {
        if a == i {
            if b == j { assert(q[a] == p[j]); assert(q[b] == p[i]); }
            else { assert(q[a] == p[j]); assert(q[b] == p[b]); }
        } else if a == j {
            assert(q[a] == p[i]);
            if b == i { } else { assert(q[b] == p[b]); }
        } else {
            assert(q[a] == p[a]);
            if b == i { assert(q[b] == p[j]); }
            else if b == j { assert(q[b] == p[i]); }
            else { assert(q[b] == p[b]); }
        }
    }
}



proof fn lemma_max_dp_before_nonneg(ss: Seq<i32>, i: int, bound: i32)
    requires 0 <= i <= ss.len(),
    ensures max_dp_before(ss, i, bound) >= 0,
    decreases i, 0nat,
{
    if i > 0 {
        lemma_max_dp_before_nonneg(ss, i - 1, bound);
    }
}

proof fn lemma_dp_at_pos(ss: Seq<i32>, i: int)
    requires 0 <= i < ss.len(), 1 <= ss[i],
    ensures dp_at(ss, i) >= ss[i] as int, dp_at(ss, i) >= 1,
{
    lemma_max_dp_before_nonneg(ss, i, ss[i]);
}

proof fn lemma_max_dp_before_includes(ss: Seq<i32>, i: int, bound: i32, j: int)
    requires
        0 <= j < i, j < ss.len(), ss[j] <= bound,
    ensures
        max_dp_before(ss, i, bound) >= dp_at(ss, j),
    decreases i, 0nat,
{
    if i > j + 1 {
        lemma_max_dp_before_includes(ss, i - 1, bound, j);
    }
}

proof fn lemma_overall_best_includes(ss: Seq<i32>, end: int, i: int)
    requires 0 <= i < end, end <= ss.len(),
    ensures overall_best(ss, end) >= dp_at(ss, i),
    decreases end,
{
    if i < end - 1 {
        lemma_overall_best_includes(ss, end - 1, i);
    }
}

proof fn lemma_max_dp_before_bound(ss: Seq<i32>, i: int, bound: i32)
    requires
        0 <= i <= ss.len(),
        forall|k: int| 0 <= k < ss.len() ==> 1 <= #[trigger] ss[k] <= 1_000_000,
    ensures max_dp_before(ss, i, bound) <= i as int * 1_000_000,
    decreases i, 0nat,
{
    if i > 0 {
        lemma_max_dp_before_bound(ss, i - 1, bound);
        if ss[i - 1] <= bound {
            lemma_dp_at_bound(ss, i - 1);
        }
    }
}

proof fn lemma_dp_at_bound(ss: Seq<i32>, i: int)
    requires
        0 <= i < ss.len(),
        forall|k: int| 0 <= k < ss.len() ==> 1 <= #[trigger] ss[k] <= 1_000_000,
    ensures dp_at(ss, i) <= (i + 1) as int * 1_000_000,
    decreases i, 1nat,
{
    lemma_max_dp_before_bound(ss, i, ss[i]);
}

proof fn lemma_overall_best_bound(ss: Seq<i32>, end: int)
    requires
        0 < end <= ss.len(),
        forall|k: int| 0 <= k < ss.len() ==> 1 <= #[trigger] ss[k] <= 1_000_000,
    ensures
        overall_best(ss, end) >= 1,
        overall_best(ss, end) <= end as int * 1_000_000,
    decreases end,
{
    lemma_dp_at_pos(ss, end - 1);
    lemma_dp_at_bound(ss, end - 1);
    if end > 1 {
        lemma_overall_best_bound(ss, end - 1);
    }
}



proof fn lemma_max_dp_before_witness(ss: Seq<i32>, i: int, bound: i32) -> (j: int)
    requires
        0 <= i <= ss.len(),
        max_dp_before(ss, i, bound) > 0,
    ensures
        0 <= j < i,
        j < ss.len(),
        ss[j] <= bound,
        dp_at(ss, j) == max_dp_before(ss, i, bound),
    decreases i, 0nat,
{
    if i <= 0 {
        0  
    } else {
        let rest = max_dp_before(ss, i - 1, bound);
        if ss[i - 1] <= bound {
            let cur = dp_at(ss, i - 1);
            if cur > rest {
                i - 1
            } else if rest > 0 {
                lemma_max_dp_before_witness(ss, i - 1, bound)
            } else {
                i - 1
            }
        } else {
            lemma_max_dp_before_witness(ss, i - 1, bound)
        }
    }
}

proof fn lemma_overall_best_witness(ss: Seq<i32>, end: int) -> (i: int)
    requires
        0 < end <= ss.len(),
        forall|k: int| 0 <= k < ss.len() ==> 1 <= #[trigger] ss[k] <= 1_000_000,
    ensures
        0 <= i < end,
        dp_at(ss, i) == overall_best(ss, end),
    decreases end,
{
    if end == 1 {
        lemma_dp_at_pos(ss, 0);
        assert(overall_best(ss, 0) == 0);
        assert(dp_at(ss, 0) >= 1);
        assert(overall_best(ss, 1) == dp_at(ss, 0));
        0
    } else {
        let prev = overall_best(ss, end - 1);
        let cur = dp_at(ss, end - 1);
        if cur > prev {
            end - 1
        } else {
            lemma_overall_best_witness(ss, end - 1)
        }
    }
}

proof fn lemma_dp_at_team(
    ss: Seq<i32>, aa: Seq<i32>, perm: Seq<int>, inv: Seq<int>,
    orig_s: Seq<i32>, orig_a: Seq<i32>, n: int, i: int,
) -> (team: Seq<int>)
    requires
        0 <= i < n,
        n >= 1,
        ss.len() == n, aa.len() == n, perm.len() == n, inv.len() == n,
        orig_s.len() == n, orig_a.len() == n,
        is_index_permutation(perm, n),
        forall|k: int| 0 <= k < n ==> 0 <= #[trigger] inv[k] < n,
        forall|k: int| 0 <= k < n ==> inv[#[trigger] perm[k]] == k,
        forall|k: int| 0 <= k < n ==> perm[#[trigger] inv[k]] == k,
        forall|k: int| 0 <= k < n ==> ss[k] == orig_s[#[trigger] perm[k]],
        forall|k: int| 0 <= k < n ==> aa[k] == orig_a[#[trigger] perm[k]],
        sorted_by_age_score(aa, ss),
        forall|k: int| 0 <= k < n ==> 1 <= #[trigger] ss[k] <= 1_000_000,
    ensures
        team.len() >= 1,
        is_valid_team(team, orig_s, orig_a),
        team_score_sum(team, orig_s) == dp_at(ss, i),
        team.last() == perm[i],
        forall|k: int| 0 <= k < team.len() ==> 0 <= inv[#[trigger] team[k]] <= i,
        forall|k: int| 0 <= k < team.len()
            ==> orig_s[#[trigger] team[k]] as int <= ss[i] as int,
    decreases i, 1nat,
{
    let mlb = max_dp_before(ss, i, ss[i]);
    if mlb <= 0 {
        lemma_max_dp_before_nonneg(ss, i, ss[i]);
        let team: Seq<int> = seq![perm[i]];
        assert(team.len() == 1);
        assert(team[0] == perm[i]);
        assert(team.last() == perm[i]);
        assert(team.drop_last() =~= Seq::<int>::empty());
        assert(team_score_sum(team.drop_last(), orig_s) == 0);
        assert(team_score_sum(team, orig_s) == orig_s[perm[i]] as int);
        assert(orig_s[perm[i]] as int == ss[i] as int);
        assert(dp_at(ss, i) == ss[i] as int + mlb);
        assert(mlb == 0);

        
        assert forall|k: int| 0 <= k < team.len()
            implies 0 <= #[trigger] team[k] < orig_s.len() as int by {}
        assert forall|k: int, l: int| 0 <= k < l < team.len()
            implies team[k] != team[l] by {}
        assert forall|k: int, l: int|
            0 <= k < team.len() && 0 <= l < team.len()
            implies (orig_a[team[k]] < orig_a[team[l]]
                ==> orig_s[team[k]] <= orig_s[team[l]]) by {}

        assert(inv[team[0]] == inv[perm[i]] == i);
        team
    } else {
        let j = lemma_max_dp_before_witness(ss, i, ss[i]);
        let prev_team = lemma_dp_at_team(ss, aa, perm, inv, orig_s, orig_a, n, j);
        let team = prev_team.push(perm[i]);

        
        assert(team.last() == perm[i]);
        assert(team.drop_last() =~= prev_team);
        assert(team_score_sum(team, orig_s)
            == orig_s[perm[i]] as int + team_score_sum(prev_team, orig_s));
        assert(orig_s[perm[i]] as int == ss[i] as int);
        assert(team_score_sum(prev_team, orig_s) == dp_at(ss, j));
        assert(dp_at(ss, j) == mlb);
        assert(dp_at(ss, i) == ss[i] as int + mlb);

        
        assert forall|k: int| 0 <= k < team.len()
            implies 0 <= inv[#[trigger] team[k]] <= i by {
            if k < prev_team.len() {
                assert(team[k] == prev_team[k]);
                assert(inv[prev_team[k]] <= j);
                assert(j < i);
            } else {
                assert(team[k] == perm[i]);
                assert(inv[perm[i]] == i);
            }
        }

        
        assert forall|k: int| 0 <= k < team.len()
            implies orig_s[#[trigger] team[k]] as int <= ss[i] as int by {
            if k < prev_team.len() {
                assert(team[k] == prev_team[k]);
                assert(orig_s[prev_team[k]] as int <= ss[j] as int);
                assert(ss[j] <= ss[i]);
            } else {
                assert(team[k] == perm[i]);
                assert(orig_s[perm[i]] as int == ss[i] as int);
            }
        }

        
        assert forall|k: int| 0 <= k < team.len()
            implies 0 <= #[trigger] team[k] < orig_s.len() as int by {
            if k < prev_team.len() {
                assert(team[k] == prev_team[k]);
            } else {
                assert(team[k] == perm[i]);
                assert(0 <= perm[i] < n);
            }
        }

        
        assert forall|k: int, l: int| 0 <= k < l < team.len()
            implies team[k] != team[l] by {
            if l < prev_team.len() {
                assert(team[k] == prev_team[k]);
                assert(team[l] == prev_team[l]);
            } else {
                assert(team[l] == perm[i]);
                assert(team[k] == prev_team[k]);
                assert(inv[prev_team[k]] <= j);
                assert(inv[perm[i]] == i);
                assert(j < i);
                
            }
        }

        
        assert forall|k: int, l: int|
            0 <= k < team.len() && 0 <= l < team.len()
            implies (orig_a[team[k]] < orig_a[team[l]]
                ==> orig_s[team[k]] <= orig_s[team[l]]) by {
            if k < prev_team.len() && l < prev_team.len() {
                
                assert(team[k] == prev_team[k]);
                assert(team[l] == prev_team[l]);
            } else if k < prev_team.len() && l == prev_team.len() {
                
                assert(team[k] == prev_team[k]);
                assert(team[l] == perm[i]);
                let pk = inv[prev_team[k]];
                assert(orig_a[prev_team[k]] == aa[pk]);
                assert(orig_a[perm[i]] == aa[i]);
                assert(orig_s[prev_team[k]] as int <= ss[i] as int);
                assert(orig_s[perm[i]] as int == ss[i] as int);
                
            } else if k == prev_team.len() && l < prev_team.len() {
                
                assert(team[k] == perm[i]);
                assert(team[l] == prev_team[l]);
                let pl = inv[prev_team[l]];
                assert(orig_a[perm[i]] == aa[i]);
                assert(orig_a[prev_team[l]] == aa[pl]);
                assert(pl <= j);
                assert(j < i);
                
                
                assert(aa[pl] < aa[i] || (aa[pl] == aa[i] && ss[pl] <= ss[i]));
            } else {
                
            }
        }

        team
    }
}



proof fn lemma_team_score_sum_update(s: Seq<int>, scores: Seq<i32>, k: int, new_val: int)
    requires
        s.len() >= 1,
        0 <= k < s.len(),
        0 <= new_val < scores.len(),
        forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] < scores.len(),
    ensures
        team_score_sum(s.update(k, new_val), scores) ==
            team_score_sum(s, scores) - scores[s[k]] as int + scores[new_val] as int,
    decreases s.len(),
{
    if s.len() == 1 {
        assert(k == 0);
        let updated = s.update(0, new_val);
        
        assert(updated.len() == 1);
        assert(updated.last() == new_val);
        assert(updated.drop_last() =~= Seq::<int>::empty());
        assert(team_score_sum(Seq::<int>::empty(), scores) == 0) by {
            assert(Seq::<int>::empty().len() == 0);
        }
        
        assert(s.last() == s[0]);
        assert(s.drop_last() =~= Seq::<int>::empty());
    } else if k == s.len() - 1 {
        assert(s.update(k, new_val).drop_last() =~= s.drop_last());
    } else {
        assert(s.update(k, new_val).drop_last() =~= s.drop_last().update(k, new_val));
        lemma_team_score_sum_update(s.drop_last(), scores, k, new_val);
    }
}

proof fn lemma_max_inv_idx_props(team: Seq<int>, inv: Seq<int>)
    requires
        team.len() >= 1,
        forall|k: int| 0 <= k < team.len() ==> 0 <= #[trigger] team[k] < inv.len(),
    ensures
        0 <= max_inv_idx(team, inv) < team.len(),
        forall|k: int| 0 <= k < team.len()
            ==> inv[#[trigger] team[k]] <= inv[team[max_inv_idx(team, inv)]],
    decreases team.len(),
{
    if team.len() > 1 {
        lemma_max_inv_idx_props(team.drop_last(), inv);
        let prev = max_inv_idx(team.drop_last(), inv);
        assert forall|k: int| 0 <= k < team.len()
            implies inv[#[trigger] team[k]] <= inv[team[max_inv_idx(team, inv)]] by {
            if k < team.len() - 1 {
                assert(team.drop_last()[k] == team[k]);
                assert(inv[team[k]] <= inv[team.drop_last()[prev]]);
                assert(team.drop_last()[prev] == team[prev]);
            }
        }
    }
}

proof fn lemma_swap_drop_last_valid(
    team: Seq<int>, scores: Seq<i32>, ages: Seq<i32>, k: int,
)
    requires
        is_valid_team(team, scores, ages),
        0 <= k < team.len(),
        team.len() >= 2,
    ensures ({
        let swapped = team.update(k, team[team.len() - 1])
                         .update(team.len() - 1, team[k]);
        let smaller = swapped.drop_last();
        is_valid_team(smaller, scores, ages)
    }),
{
    let swapped = team.update(k, team[team.len() - 1])
                     .update(team.len() - 1, team[k]);
    let smaller = swapped.drop_last();
    let n = team.len();

    
    
    

    
    assert forall|j: int| 0 <= j < smaller.len()
        implies 0 <= #[trigger] smaller[j] < scores.len() as int by {
        let orig = if j == k { n - 1 } else { j };
        assert(smaller[j] == team[orig]);
    }

    
    assert forall|a: int, b: int| 0 <= a < b < smaller.len()
        implies smaller[a] != smaller[b] by {
        let a_orig: int = if a == k { n - 1 } else { a };
        let b_orig: int = if b == k { n - 1 } else { b };
        assert(smaller[a] == team[a_orig]);
        assert(smaller[b] == team[b_orig]);
        assert(a_orig != b_orig);
        if a_orig < b_orig {
            assert(team[a_orig] != team[b_orig]);
        } else {
            assert(team[b_orig] != team[a_orig]);
        }
    }

    
    assert forall|a: int, b: int|
        0 <= a < smaller.len() && 0 <= b < smaller.len()
        implies (ages[smaller[a]] < ages[smaller[b]]
            ==> scores[smaller[a]] <= scores[smaller[b]]) by {
        let a_orig: int = if a == k { n - 1 } else { a };
        let b_orig: int = if b == k { n - 1 } else { b };
        assert(smaller[a] == team[a_orig]);
        assert(smaller[b] == team[b_orig]);
        assert(0 <= a_orig < team.len());
        assert(0 <= b_orig < team.len());
        
        assert(ages[team[a_orig]] < ages[team[b_orig]]
            ==> scores[team[a_orig]] <= scores[team[b_orig]]);
    }
}



proof fn lemma_valid_team_bounded(
    team: Seq<int>, orig_s: Seq<i32>, orig_a: Seq<i32>,
    ss: Seq<i32>, aa: Seq<i32>, perm: Seq<int>, inv: Seq<int>, n: int,
) -> (pos: int)
    requires
        team.len() >= 1,
        is_valid_team(team, orig_s, orig_a),
        n >= 1,
        orig_s.len() == n, orig_a.len() == n, ss.len() == n, aa.len() == n,
        perm.len() == n, inv.len() == n,
        is_index_permutation(perm, n),
        forall|k: int| 0 <= k < n ==> 0 <= #[trigger] inv[k] < n,
        forall|k: int| 0 <= k < n ==> inv[#[trigger] perm[k]] == k,
        forall|k: int| 0 <= k < n ==> perm[#[trigger] inv[k]] == k,
        forall|k: int| 0 <= k < n ==> ss[k] == orig_s[#[trigger] perm[k]],
        forall|k: int| 0 <= k < n ==> aa[k] == orig_a[#[trigger] perm[k]],
        sorted_by_age_score(aa, ss),
        forall|k: int| 0 <= k < n ==> 1 <= #[trigger] ss[k] <= 1_000_000,
    ensures
        0 <= pos < n,
        team_score_sum(team, orig_s) <= dp_at(ss, pos),
        exists|m: int| 0 <= m < team.len() && inv[#[trigger] team[m]] == pos,
    decreases team.len(),
{
    lemma_max_inv_idx_props(team, inv);
    let max_k = max_inv_idx(team, inv);
    let max_elem = team[max_k];
    let max_pos = inv[max_elem];

    if team.len() == 1 {
        lemma_dp_at_pos(ss, max_pos as int);
        assert(team.last() == team[0]);
        assert(team.drop_last() =~= Seq::<int>::empty());
        assert(team_score_sum(team.drop_last(), orig_s) == 0);
        assert(team_score_sum(team, orig_s) == orig_s[team.last()] as int + 0);
        assert(team[0] == max_elem);
        assert(orig_s[max_elem] as int == ss[max_pos] as int);
        assert(dp_at(ss, max_pos as int) >= ss[max_pos] as int);
        max_pos as int
    } else {
        
        let swapped = team.update(max_k, team[team.len() - 1])
                         .update(team.len() - 1, team[max_k]);
        let smaller = swapped.drop_last();

        
        if max_k == team.len() - 1 {
            assert(swapped =~= team);
        } else {
            
            lemma_team_score_sum_update(team, orig_s, max_k, team[team.len() - 1]);
            let intermediate = team.update(max_k, team[team.len() - 1]);
            
            assert forall|ii: int| 0 <= ii < intermediate.len()
                implies 0 <= #[trigger] intermediate[ii] < orig_s.len() by {
                if ii == max_k as int {
                    assert(intermediate[ii] == team[team.len() - 1]);
                } else {
                    assert(intermediate[ii] == team[ii]);
                }
            }
            lemma_team_score_sum_update(
                intermediate, orig_s,
                team.len() - 1, team[max_k]);
            assert(intermediate[team.len() - 1] == team[team.len() - 1]);
            
            
            
            assert(swapped =~= intermediate.update(team.len() - 1, team[max_k]));
        }

        
        assert(swapped.last() == team[max_k]);
        assert(swapped.drop_last() =~= smaller);
        assert(team_score_sum(swapped, orig_s)
            == orig_s[team[max_k]] as int + team_score_sum(smaller, orig_s));
        assert(orig_s[team[max_k]] as int == ss[max_pos] as int);

        
        lemma_swap_drop_last_valid(team, orig_s, orig_a, max_k);

        
        let prev_pos = lemma_valid_team_bounded(
            smaller, orig_s, orig_a, ss, aa, perm, inv, n);

        
        let prev_m = choose|m: int| 0 <= m < smaller.len()
            && inv[#[trigger] smaller[m]] == prev_pos;

        
        
        let orig_idx: int = if prev_m == max_k { team.len() - 1 } else { prev_m };
        assert(smaller[prev_m] == team[orig_idx]);
        assert(inv[team[orig_idx]] <= max_pos);
        
        
        assert(orig_idx != max_k as int);
        if orig_idx < max_k {
            assert(team[orig_idx] != team[max_k]);
        } else {
            assert(team[max_k] != team[orig_idx]);
        }
        assert(team[orig_idx] != max_elem);
        
        
        assert(perm[inv[team[orig_idx]]] == team[orig_idx]);
        assert(perm[max_pos as int] == max_elem);
        assert(inv[team[orig_idx]] != max_pos);
        assert(prev_pos < max_pos);

        
        
        
        
        
        assert(aa[prev_pos] < aa[max_pos]
            || (aa[prev_pos] == aa[max_pos] && ss[prev_pos] <= ss[max_pos]));
        if aa[prev_pos] < aa[max_pos] {
            
            
            assert(orig_a[team[orig_idx]] == aa[prev_pos]);
            assert(orig_a[max_elem] == aa[max_pos]);
            
            assert(orig_a[team[orig_idx]] < orig_a[max_elem]);
            assert(orig_s[team[orig_idx]] <= orig_s[max_elem]);
            assert(ss[prev_pos] == orig_s[perm[prev_pos]] == orig_s[team[orig_idx]]);
            assert(ss[max_pos] == orig_s[perm[max_pos as int]] == orig_s[max_elem]);
        }
        assert(ss[prev_pos] <= ss[max_pos]);

        
        lemma_max_dp_before_includes(ss, max_pos as int, ss[max_pos as int], prev_pos);

        
        
        

        max_pos as int
    }
}



impl Solution {
    pub fn best_team_score(scores: Vec<i32>, ages: Vec<i32>) -> (res: i32)
        requires
            1 <= scores.len() <= 1000,
            scores.len() == ages.len(),
            forall|i: int| 0 <= i < scores.len() ==> 1 <= #[trigger] scores[i] <= 1_000_000,
            forall|i: int| 0 <= i < ages.len() ==> 1 <= #[trigger] ages[i] <= 1000,
        ensures
            res >= 1,
            exists|team: Seq<int>| is_valid_team(team, scores@, ages@)
                && team_score_sum(team, scores@) == res as int,
            forall|team: Seq<int>| is_valid_team(team, scores@, ages@)
                ==> team_score_sum(team, scores@) <= res as int,
    {
        let ghost orig_scores = scores@;
        let ghost orig_ages = ages@;
        let n = scores.len();
        let mut scores = scores;
        let mut ages = ages;

        let ghost mut perm: Seq<int> = Seq::new(n as nat, |i: int| i);
        let ghost mut inv: Seq<int> = Seq::new(n as nat, |i: int| i);

        
        let mut i: usize = 0;
        while i < n
            invariant
                n == scores.len(),
                n == ages.len(),
                orig_scores.len() == n,
                orig_ages.len() == n,
                1 <= n <= 1000,
                0 <= i <= n,
                perm.len() == n,
                inv.len() == n,
                is_index_permutation(perm, n as int),
                forall|k: int| 0 <= k < n ==> 0 <= #[trigger] inv[k] < n,
                forall|k: int| 0 <= k < n
                    ==> inv[#[trigger] perm[k]] == k,
                forall|k: int| 0 <= k < n
                    ==> perm[#[trigger] inv[k]] == k,
                forall|k: int| 0 <= k < n
                    ==> scores[k] == orig_scores[#[trigger] perm[k]],
                forall|k: int| 0 <= k < n
                    ==> ages[k] == orig_ages[#[trigger] perm[k]],
                forall|k: int| 0 <= k < n
                    ==> 1 <= #[trigger] scores[k] <= 1_000_000,
                forall|k: int| 0 <= k < n
                    ==> 1 <= #[trigger] ages[k] <= 1000,
                forall|a: int, b: int| 0 <= a < b < i
                    ==> (ages[a] < ages[b]
                        || (ages[a] == ages[b] && scores[a] <= scores[b])),
                forall|a: int, b: int| 0 <= a < i && i <= b < n
                    ==> (ages[a] < ages[b]
                        || (ages[a] == ages[b] && scores[a] <= scores[b])),
            decreases n - i,
        {
            let mut min_idx = i;
            let mut j = i + 1;
            while j < n
                invariant
                    n == scores.len(),
                    n == ages.len(),
                    1 <= n <= 1000,
                    i < n,
                    i <= min_idx < n,
                    i + 1 <= j <= n,
                    forall|k: int| 0 <= k < n
                        ==> 1 <= #[trigger] scores[k] <= 1_000_000,
                    forall|k: int| 0 <= k < n
                        ==> 1 <= #[trigger] ages[k] <= 1000,
                    forall|k: int| i <= k < j
                        ==> (ages[min_idx as int] < ages[k]
                            || (ages[min_idx as int] == ages[k]
                                && scores[min_idx as int] <= scores[k])),
                decreases n - j,
            {
                if ages[j] < ages[min_idx]
                    || (ages[j] == ages[min_idx] && scores[j] < scores[min_idx])
                {
                    min_idx = j;
                }
                j += 1;
            }

            let old_i = i;
            let old_min_idx = min_idx;
            let tmp_a = ages[i];
            let tmp_s = scores[i];
            let ghost old_perm = perm;
            let ghost old_inv = inv;
            ages[i] = ages[min_idx];
            scores[i] = scores[min_idx];
            ages[min_idx] = tmp_a;
            scores[min_idx] = tmp_s;

            proof {
                perm = old_perm.update(old_i as int, old_perm[old_min_idx as int])
                    .update(old_min_idx as int, old_perm[old_i as int]);
                inv = old_inv.update(old_perm[old_min_idx as int], old_i as int)
                    .update(old_perm[old_i as int], old_min_idx as int);

                lemma_swap_preserves_index_permutation(
                    old_perm, old_i as int, old_min_idx as int, n as int);

                
                assert forall|k: int| 0 <= k < n implies
                    scores[k] == orig_scores[#[trigger] perm[k]]
                    && ages[k] == orig_ages[perm[k]] by {
                    if k == old_i as int {
                        assert(perm[k] == old_perm[old_min_idx as int]);
                    } else if k == old_min_idx as int {
                        assert(perm[k] == old_perm[old_i as int]);
                    } else {
                        assert(perm[k] == old_perm[k]);
                    }
                }

                
                assert forall|k: int| 0 <= k < n implies 0 <= #[trigger] inv[k] < n by {
                    if k == old_perm[old_min_idx as int] {
                        assert(inv[k] == old_i as int);
                    } else if k == old_perm[old_i as int] {
                        assert(inv[k] == old_min_idx as int);
                    } else {
                        assert(inv[k] == old_inv[k]);
                    }
                }

                
                assert forall|k: int| 0 <= k < n implies
                    inv[#[trigger] perm[k]] == k by {
                    if k == old_i as int {
                        assert(perm[k] == old_perm[old_min_idx as int]);
                        assert(inv[old_perm[old_min_idx as int]] == old_i as int);
                    } else if k == old_min_idx as int {
                        assert(perm[k] == old_perm[old_i as int]);
                        if old_perm[old_i as int] == old_perm[old_min_idx as int] {
                            
                        } else {
                            assert(inv[old_perm[old_i as int]] == old_min_idx as int);
                        }
                    } else {
                        assert(perm[k] == old_perm[k]);
                        if old_perm[k] == old_perm[old_min_idx as int] {
                            
                        } else if old_perm[k] == old_perm[old_i as int] {
                            
                        } else {
                            assert(inv[old_perm[k]] == old_inv[old_perm[k]] == k);
                        }
                    }
                }
                assert forall|k: int| 0 <= k < n implies
                    perm[#[trigger] inv[k]] == k by {
                    let pk = inv[k];
                    assert(inv[perm[pk]] == pk);
                    assert(perm[pk] == k || inv[perm[pk]] != pk);
                    
                    
                    
                    if k == old_perm[old_min_idx as int] {
                        assert(inv[k] == old_i as int);
                        assert(perm[old_i as int] == old_perm[old_min_idx as int] == k);
                    } else if k == old_perm[old_i as int] {
                        if old_perm[old_i as int] == old_perm[old_min_idx as int] {
                        } else {
                            assert(inv[k] == old_min_idx as int);
                            assert(perm[old_min_idx as int]
                                == old_perm[old_i as int] == k);
                        }
                    } else {
                        assert(inv[k] == old_inv[k]);
                        let ik = old_inv[k];
                        assert(old_perm[ik] == k);
                        assert(ik != old_i as int);
                        assert(ik != old_min_idx as int);
                        assert(perm[ik] == old_perm[ik] == k);
                    }
                }

                
                assert forall|a: int, b: int| 0 <= a < b < old_i + 1 implies
                    (ages[a] < ages[b]
                        || (ages[a] == ages[b] && scores[a] <= scores[b])) by {
                    if b < old_i {
                    } else {
                        assert(b == old_i);
                        if a < old_i {
                            
                            
                            
                            
                        }
                    }
                }

                
                assert forall|a: int, b: int|
                    0 <= a < old_i + 1 && old_i + 1 <= b < n implies
                    (ages[a] < ages[b]
                        || (ages[a] == ages[b] && scores[a] <= scores[b])) by {
                    if a < old_i {
                        
                        if b == old_min_idx as int {
                            
                            
                        } else {
                            
                            
                        }
                    } else {
                        assert(a == old_i);
                        
                        if b == old_min_idx as int {
                            
                            
                            
                        } else {
                            
                            
                            
                        }
                    }
                }

                
                assert forall|k: int| 0 <= k < n implies
                    1 <= #[trigger] scores[k] <= 1_000_000 by {
                    if k == old_i as int {
                    } else if k == old_min_idx as int {
                    } else {
                    }
                }
                assert forall|k: int| 0 <= k < n implies
                    1 <= #[trigger] ages[k] <= 1000 by {
                    if k == old_i as int {
                    } else if k == old_min_idx as int {
                    } else {
                    }
                }
            }
            i += 1;
        }

        proof {
            assert(sorted_by_age_score(ages@, scores@));
        }

        
        let mut dp: Vec<i64> = Vec::new();
        i = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == scores.len(),
                dp.len() == i,
                forall|j: int| 0 <= j < i ==> dp[j] == scores[j] as i64,
            decreases n - i,
        {
            dp.push(scores[i] as i64);
            i += 1;
        }

        
        proof {
            lemma_dp_at_pos(scores@, 0);
            lemma_max_dp_before_nonneg(scores@, 0, scores@[0]);
        }
        i = 1;
        while i < n
            invariant
                1 <= n <= 1000,
                n == scores.len(),
                dp.len() == n,
                1 <= i <= n,
                forall|j: int| 0 <= j < i
                    ==> (#[trigger] dp[j]) as int == dp_at(scores@, j),
                forall|j: int| 0 <= j < i
                    ==> 1 <= (#[trigger] dp[j]) <= (j + 1) as i64 * 1_000_000,
                forall|j: int| i <= j < n as int
                    ==> (#[trigger] dp[j]) as i64 == scores@[j] as i64,
                forall|k: int| 0 <= k < n
                    ==> 1 <= #[trigger] scores[k] <= 1_000_000,
            decreases n - i,
        {
            let mut j: usize = 0;
            while j < i
                invariant
                    1 <= n <= 1000,
                    n == scores.len(),
                    dp.len() == n,
                    1 <= i < n,
                    0 <= j <= i,
                    forall|k: int| 0 <= k < i
                        ==> (#[trigger] dp[k]) as int == dp_at(scores@, k),
                    forall|k: int| 0 <= k < i
                        ==> 1 <= (#[trigger] dp[k]) <= (k + 1) as i64 * 1_000_000,
                    forall|k: int| i < k < n as int
                        ==> (#[trigger] dp[k]) as i64 == scores@[k] as i64,
                    dp[i as int] as int == scores@[i as int] as int
                        + max_dp_before(scores@, j as int, scores@[i as int]),
                    1 <= dp[i as int] <= (i as int + 1) as i64 * 1_000_000,
                    forall|k: int| 0 <= k < n
                        ==> 1 <= #[trigger] scores[k] <= 1_000_000,
                decreases i - j,
            {
                if scores[j] <= scores[i] {
                    if dp[j] + scores[i] as i64 > dp[i] {
                        dp.set(i, dp[j] + scores[i] as i64);
                    }
                }
                j += 1;
            }
            proof {
                assert(dp[i as int] as int == scores@[i as int] as int
                    + max_dp_before(scores@, i as int, scores@[i as int]));
                assert(dp_at(scores@, i as int) == scores@[i as int] as int
                    + max_dp_before(scores@, i as int, scores@[i as int]));
                lemma_dp_at_bound(scores@, i as int);
                lemma_dp_at_pos(scores@, i as int);
            }
            i += 1;
        }

        
        let mut best: i64 = dp[0];
        proof {
            assert(dp[0] as int == dp_at(scores@, 0));
            lemma_dp_at_pos(scores@, 0);
            assert(dp_at(scores@, 0) >= 1);
            assert(overall_best(scores@, 0) == 0);
            
            
        }
        let mut k: usize = 1;
        while k < n
            invariant
                1 <= n <= 1000,
                n == scores.len(),
                dp.len() == n,
                1 <= k <= n,
                forall|j: int| 0 <= j < n
                    ==> (#[trigger] dp[j]) as int == dp_at(scores@, j),
                forall|j: int| 0 <= j < n
                    ==> 1 <= (#[trigger] dp[j]) <= (j + 1) as i64 * 1_000_000,
                best as int == overall_best(scores@, k as int),
                1 <= best <= n as i64 * 1_000_000,
            decreases n - k,
        {
            if dp[k] > best {
                best = dp[k];
            }
            k += 1;
        }

        
        proof {
            lemma_overall_best_bound(scores@, n as int);
            assert(best as int == overall_best(scores@, n as int));
            assert(1 <= best);
            assert(best <= n as i64 * 1_000_000);
            assert(best <= 1_000_000_000i64) by (nonlinear_arith)
                requires n <= 1000, best <= n as i64 * 1_000_000;

            
            let best_pos = lemma_overall_best_witness(scores@, n as int);
            let team = lemma_dp_at_team(
                scores@, ages@, perm, inv,
                orig_scores, orig_ages, n as int, best_pos);
            assert(is_valid_team(team, orig_scores, orig_ages));
            assert(team_score_sum(team, orig_scores) == dp_at(scores@, best_pos));
            assert(dp_at(scores@, best_pos) == overall_best(scores@, n as int));
            assert(team_score_sum(team, orig_scores) == best as int);

            
            assert forall|t: Seq<int>| is_valid_team(t, orig_scores, orig_ages)
                implies team_score_sum(t, orig_scores) <= best as int by {
                if t.len() == 0 {
                    assert(team_score_sum(t, orig_scores) == 0);
                } else {
                    let pos = lemma_valid_team_bounded(
                        t, orig_scores, orig_ages,
                        scores@, ages@, perm, inv, n as int);
                    lemma_overall_best_includes(scores@, n as int, pos);
                }
            }
        }
        best as i32
    }
}

}
