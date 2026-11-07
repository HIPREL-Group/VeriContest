use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn all_indices_distinct(left_idx: Seq<int>, right_idx: Seq<int>) -> bool {
    &&& forall |i: int, j: int| 0 <= i < j < left_idx.len()
        ==> left_idx[i] != left_idx[j]
    &&& forall |i: int, j: int| 0 <= i < j < right_idx.len()
        ==> right_idx[i] != right_idx[j]
    &&& forall |i: int, j: int| 0 <= i < left_idx.len() && 0 <= j < right_idx.len()
        ==> left_idx[i] != right_idx[j]
}

pub open spec fn is_valid_matching(nums: Seq<i32>, left_idx: Seq<int>, right_idx: Seq<int>, k: int) -> bool {
    &&& left_idx.len() == right_idx.len()
    &&& forall |i: int| 0 <= i < left_idx.len() ==> {
        &&& 0 <= left_idx[i] < nums.len()
        &&& 0 <= right_idx[i] < nums.len()
        &&& left_idx[i] != right_idx[i]
        &&& nums[left_idx[i]] as int + nums[right_idx[i]] as int == k
    }
    &&& all_indices_distinct(left_idx, right_idx)
}


pub open spec fn max_k_sum_pairs(s: Seq<i32>, k: int, lo: int, hi: int) -> int
    decreases (if hi > lo { hi - lo } else { 0 }),
{
    if lo >= hi {
        0
    } else {
        if s[lo] as int + s[hi] as int == k {
            1 + max_k_sum_pairs(s, k, lo + 1, hi - 1)
        } else {
            if (s[lo] as int + s[hi] as int) < k {
                max_k_sum_pairs(s, k, lo + 1, hi)
            } else {
                max_k_sum_pairs(s, k, lo, hi - 1)
            }
        }
    }
}


pub open spec fn matching_left(s: Seq<i32>, k: int, lo: int, hi: int) -> Seq<int>
    decreases (if hi > lo { hi - lo } else { 0 }),
{
    if lo >= hi { Seq::<int>::empty() }
    else if s[lo] as int + s[hi] as int == k { seq![lo] + matching_left(s, k, lo + 1, hi - 1) }
    else if (s[lo] as int + s[hi] as int) < k { matching_left(s, k, lo + 1, hi) }
    else { matching_left(s, k, lo, hi - 1) }
}

pub open spec fn matching_right(s: Seq<i32>, k: int, lo: int, hi: int) -> Seq<int>
    decreases (if hi > lo { hi - lo } else { 0 }),
{
    if lo >= hi { Seq::<int>::empty() }
    else if s[lo] as int + s[hi] as int == k { seq![hi] + matching_right(s, k, lo + 1, hi - 1) }
    else if (s[lo] as int + s[hi] as int) < k { matching_right(s, k, lo + 1, hi) }
    else { matching_right(s, k, lo, hi - 1) }
}

pub open spec fn dec_val(left: int, right: int) -> nat {
    if right > left { (right - left) as nat } else { 0 }
}

pub open spec fn seq_remove_at(s: Seq<int>, p: int) -> Seq<int> {
    Seq::new(
        if s.len() > 0 { (s.len() - 1) as nat } else { 0 },
        |i: int| s[if i < p { i } else { i + 1 }],
    )
}

proof fn max_k_sum_pairs_bound(s: Seq<i32>, k: int, lo: int, hi: int)
    requires 0 <= lo, hi < s.len(),
    ensures
        max_k_sum_pairs(s, k, lo, hi) >= 0,
        lo <= hi ==> 2 * max_k_sum_pairs(s, k, lo, hi) <= hi - lo + 1,
    decreases (if hi > lo { hi - lo } else { 0 }),
{
    if lo >= hi {} else {
        if s[lo] as int + s[hi] as int == k { max_k_sum_pairs_bound(s, k, lo + 1, hi - 1); }
        else if (s[lo] as int + s[hi] as int) < k { max_k_sum_pairs_bound(s, k, lo + 1, hi); }
        else { max_k_sum_pairs_bound(s, k, lo, hi - 1); }
    }
}


proof fn lemma_algo_achievable(s: Seq<i32>, k: int, lo: int, hi: int)
    requires
        0 <= lo, hi < s.len() as int,
        forall |i: int, j: int| lo <= i <= j <= hi ==> s[i] <= s[j],
    ensures
        matching_left(s, k, lo, hi).len() == matching_right(s, k, lo, hi).len(),
        matching_left(s, k, lo, hi).len() == max_k_sum_pairs(s, k, lo, hi),
        is_valid_matching(s, matching_left(s, k, lo, hi), matching_right(s, k, lo, hi), k),
        forall |i: int| #![trigger matching_left(s, k, lo, hi)[i]]
            0 <= i < matching_left(s, k, lo, hi).len() ==> lo <= matching_left(s, k, lo, hi)[i] <= hi,
        forall |i: int| #![trigger matching_right(s, k, lo, hi)[i]]
            0 <= i < matching_right(s, k, lo, hi).len() ==> lo <= matching_right(s, k, lo, hi)[i] <= hi,
    decreases (if hi > lo { hi - lo } else { 0 })
{
    let gl = matching_left(s, k, lo, hi);
    let gr = matching_right(s, k, lo, hi);
    if lo >= hi {
        assert(gl =~= Seq::<int>::empty());
        assert(gr =~= Seq::<int>::empty());
        assert(all_indices_distinct(gl, gr));
        assert(is_valid_matching(s, gl, gr, k));
    } else if s[lo] as int + s[hi] as int == k {
        lemma_algo_achievable(s, k, lo + 1, hi - 1);
        let sub_l = matching_left(s, k, lo + 1, hi - 1);
        let sub_r = matching_right(s, k, lo + 1, hi - 1);
        assert(gl =~= seq![lo] + sub_l);
        assert(gr =~= seq![hi] + sub_r);
        assert forall |i: int| #![trigger gl[i], gr[i]] 0 <= i < gl.len() implies {
            &&& 0 <= gl[i] < s.len() &&& 0 <= gr[i] < s.len()
            &&& gl[i] != gr[i] &&& s[gl[i]] as int + s[gr[i]] as int == k
        } by { if i > 0 { assert(gl[i] == sub_l[i-1]); assert(gr[i] == sub_r[i-1]); } };
        assert forall |i: int| #![trigger gl[i]] 0 <= i < gl.len() implies lo <= gl[i] <= hi
            by { if i > 0 { assert(gl[i] == sub_l[i-1]); } };
        assert forall |i: int| #![trigger gr[i]] 0 <= i < gr.len() implies lo <= gr[i] <= hi
            by { if i > 0 { assert(gr[i] == sub_r[i-1]); } };
        assert(all_indices_distinct(gl, gr)) by {
            assert forall |i: int, j: int| 0 <= i < j < gl.len() implies gl[i] != gl[j] by {
                if i == 0 { assert(gl[j] == sub_l[j-1]); assert(lo + 1 <= sub_l[j-1]); }
                else { assert(gl[i] == sub_l[i-1]); assert(gl[j] == sub_l[j-1]); }
            };
            assert forall |i: int, j: int| 0 <= i < j < gr.len() implies gr[i] != gr[j] by {
                if i == 0 { assert(gr[j] == sub_r[j-1]); assert(sub_r[j-1] <= hi - 1); }
                else { assert(gr[i] == sub_r[i-1]); assert(gr[j] == sub_r[j-1]); }
            };
            assert forall |i: int, j: int| 0 <= i < gl.len() && 0 <= j < gr.len()
                implies gl[i] != gr[j] by {
                if i == 0 && j == 0 { assert(lo < hi); }
                else if i == 0 { assert(gr[j] == sub_r[j-1]); assert(lo + 1 <= sub_r[j-1]); }
                else if j == 0 { assert(gl[i] == sub_l[i-1]); assert(sub_l[i-1] <= hi - 1); }
                else { assert(gl[i] == sub_l[i-1]); assert(gr[j] == sub_r[j-1]); }
            };
        };
        assert(is_valid_matching(s, gl, gr, k));
    } else if (s[lo] as int + s[hi] as int) < k {
        lemma_algo_achievable(s, k, lo + 1, hi);
    } else {
        lemma_algo_achievable(s, k, lo, hi - 1);
    }
}


proof fn lemma_remove_pair_valid(
    s: Seq<i32>, li: Seq<int>, ri: Seq<int>, k: int, p: int)
    requires is_valid_matching(s, li, ri, k), 0 <= p < li.len(),
    ensures
        is_valid_matching(s, seq_remove_at(li, p), seq_remove_at(ri, p), k),
        seq_remove_at(li, p).len() == li.len() - 1,
{
    let n = li.len() as int;
    let rl = seq_remove_at(li, p);
    let rr = seq_remove_at(ri, p);

    assert(is_valid_matching(s, rl, rr, k)) by {
        assert(rl.len() == rr.len());
        assert forall |i: int| #![trigger rl[i], rr[i]] 0 <= i < rl.len() implies {
            &&& 0 <= rl[i] < s.len()
            &&& 0 <= rr[i] < s.len()
            &&& rl[i] != rr[i]
            &&& s[rl[i]] as int + s[rr[i]] as int == k
        } by {
            let o: int = if i < p { i } else { i + 1 };
            assert(rl[i] == li[o]);
            assert(rr[i] == ri[o]);
            let _l: int = li[o];
            let _r: int = ri[o];
        };
        assert(all_indices_distinct(rl, rr)) by {
            assert forall |i: int, j: int| 0 <= i < j < rl.len()
                implies rl[i] != rl[j] by {
                let oi = if i < p { i } else { i + 1 };
                let oj = if j < p { j } else { j + 1 };
                assert(oi < oj);
                let _: int = li[oi]; let _: int = li[oj];
            };
            assert forall |i: int, j: int| 0 <= i < j < rr.len()
                implies rr[i] != rr[j] by {
                let oi = if i < p { i } else { i + 1 };
                let oj = if j < p { j } else { j + 1 };
                assert(oi < oj);
                let _: int = ri[oi]; let _: int = ri[oj];
            };
            assert forall |i: int, j: int| 0 <= i < rl.len() && 0 <= j < rr.len()
                implies rl[i] != rr[j] by {
                let oi = if i < p { i } else { i + 1 };
                let oj = if j < p { j } else { j + 1 };
                let _: int = li[oi]; let _: int = ri[oj];
            };
        };
    };
}


proof fn lemma_algo_optimal(s: Seq<i32>, k: int, lo: int, hi: int,
                            left_idx: Seq<int>, right_idx: Seq<int>)
    requires
        0 <= lo, hi < s.len() as int,
        forall |i: int, j: int| lo <= i <= j <= hi ==> s[i] <= s[j],
        is_valid_matching(s, left_idx, right_idx, k),
        forall |i: int| 0 <= i < left_idx.len() ==> lo <= #[trigger] left_idx[i] <= hi,
        forall |i: int| 0 <= i < right_idx.len() ==> lo <= #[trigger] right_idx[i] <= hi,
    ensures left_idx.len() <= max_k_sum_pairs(s, k, lo, hi),
    decreases (if hi > lo { hi - lo } else { 0 })
{
    if lo >= hi {
        if left_idx.len() > 0 { assert(left_idx[0] != right_idx[0]); assert(false); }
    } else {
        let sum = s[lo] as int + s[hi] as int;
        if sum < k {
            assert forall |i: int| 0 <= i < left_idx.len()
                implies left_idx[i] != lo && right_idx[i] != lo by {
                if left_idx[i] == lo { assert(s[right_idx[i]] <= s[hi]); assert(false); }
                if right_idx[i] == lo { assert(s[left_idx[i]] <= s[hi]); assert(false); }
            };
            assert(forall |i: int| 0 <= i < left_idx.len() ==> lo + 1 <= #[trigger] left_idx[i] <= hi);
            assert(forall |i: int| 0 <= i < right_idx.len() ==> lo + 1 <= #[trigger] right_idx[i] <= hi);
            lemma_algo_optimal(s, k, lo + 1, hi, left_idx, right_idx);
        } else if sum > k {
            assert forall |i: int| 0 <= i < left_idx.len()
                implies left_idx[i] != hi && right_idx[i] != hi by {
                if left_idx[i] == hi { assert(s[right_idx[i]] >= s[lo]); assert(s[hi] as int + s[right_idx[i]] as int >= sum); assert(false); }
                if right_idx[i] == hi { assert(s[left_idx[i]] >= s[lo]); assert(s[left_idx[i]] as int + s[hi] as int >= sum); assert(false); }
            };
            assert(forall |i: int| 0 <= i < left_idx.len() ==> lo <= #[trigger] left_idx[i] <= hi - 1);
            assert(forall |i: int| 0 <= i < right_idx.len() ==> lo <= #[trigger] right_idx[i] <= hi - 1);
            lemma_algo_optimal(s, k, lo, hi - 1, left_idx, right_idx);
        } else {
            
            if left_idx.len() == 0 { max_k_sum_pairs_bound(s, k, lo + 1, hi - 1); }
            else {
                let lo_in = exists |p: int| 0 <= p < left_idx.len() && (left_idx[p] == lo || right_idx[p] == lo);
                let hi_in = exists |p: int| 0 <= p < left_idx.len() && (left_idx[p] == hi || right_idx[p] == hi);
                if !lo_in && !hi_in {
                    assert forall |i: int| 0 <= i < left_idx.len() implies lo + 1 <= #[trigger] left_idx[i] <= hi - 1 by {};
                    assert forall |i: int| 0 <= i < right_idx.len() implies lo + 1 <= #[trigger] right_idx[i] <= hi - 1 by {};
                    lemma_algo_optimal(s, k, lo + 1, hi - 1, left_idx, right_idx);
                    max_k_sum_pairs_bound(s, k, lo + 1, hi - 1);
                } else {
                    let p: int = if lo_in {
                        choose |p: int| 0 <= p < left_idx.len() && (left_idx[p] == lo || right_idx[p] == lo)
                    } else {
                        choose |p: int| 0 <= p < left_idx.len() && (left_idx[p] == hi || right_idx[p] == hi)
                    };
                    lemma_remove_pair_valid(s, left_idx, right_idx, k, p);
                    let new_l = seq_remove_at(left_idx, p);
                    let new_r = seq_remove_at(right_idx, p);
                    let rem_lo = exists |i: int| 0 <= i < new_l.len() && (new_l[i] == lo || new_r[i] == lo);
                    let rem_hi = exists |i: int| 0 <= i < new_l.len() && (new_l[i] == hi || new_r[i] == hi);
                    if !rem_lo && !rem_hi {
                        assert forall |i: int| 0 <= i < new_l.len() implies lo + 1 <= #[trigger] new_l[i] <= hi - 1 by {
                            let o = if i < p { i } else { i + 1 }; assert(new_l[i] == left_idx[o]);
                        };
                        assert forall |i: int| 0 <= i < new_r.len() implies lo + 1 <= #[trigger] new_r[i] <= hi - 1 by {
                            let o = if i < p { i } else { i + 1 }; assert(new_r[i] == right_idx[o]);
                        };
                        lemma_algo_optimal(s, k, lo + 1, hi - 1, new_l, new_r);
                    } else {
                        
                        let q: int = if rem_lo {
                            choose |q: int| 0 <= q < new_l.len() && (new_l[q] == lo || new_r[q] == lo)
                        } else {
                            choose |q: int| 0 <= q < new_l.len() && (new_l[q] == hi || new_r[q] == hi)
                        };
                        lemma_remove_pair_valid(s, new_l, new_r, k, q);
                        let fin_l = seq_remove_at(new_l, q);
                        let fin_r = seq_remove_at(new_r, q);
                        let orig_q = if q < p { q } else { q + 1 };
                        let partner_lo: int = if left_idx[p] == lo { right_idx[p] }
                            else if right_idx[p] == lo { left_idx[p] }
                            else if left_idx[orig_q] == lo { right_idx[orig_q] }
                            else { left_idx[orig_q] };
                        let partner_hi: int = if left_idx[p] == hi { right_idx[p] }
                            else if right_idx[p] == hi { left_idx[p] }
                            else if left_idx[orig_q] == hi { right_idx[orig_q] }
                            else { left_idx[orig_q] };
                        assert(lo + 1 <= partner_lo && partner_lo <= hi - 1);
                        assert(lo + 1 <= partner_hi && partner_hi <= hi - 1);
                        assert(s[partner_hi] as int + s[partner_lo] as int == k);
                        let aug_l = fin_l.push(partner_hi);
                        let aug_r = fin_r.push(partner_lo);
                        assert(aug_l.len() == left_idx.len() - 1);
                        assert forall |i: int| 0 <= i < fin_l.len() implies lo + 1 <= #[trigger] fin_l[i] <= hi - 1 by {
                            let qi = if i < q { i } else { i + 1 }; assert(fin_l[i] == new_l[qi]);
                            let pi = if qi < p { qi } else { qi + 1 }; assert(new_l[qi] == left_idx[pi]);
                            assert(fin_l[i] != lo && fin_l[i] != hi);
                        };
                        assert forall |i: int| 0 <= i < fin_r.len() implies lo + 1 <= #[trigger] fin_r[i] <= hi - 1 by {
                            let qi = if i < q { i } else { i + 1 }; assert(fin_r[i] == new_r[qi]);
                            let pi = if qi < p { qi } else { qi + 1 }; assert(new_r[qi] == right_idx[pi]);
                            assert(fin_r[i] != lo && fin_r[i] != hi);
                        };
                        assert forall |i: int| #![trigger aug_l[i], aug_r[i]] 0 <= i < aug_l.len() implies {
                            &&& 0 <= aug_l[i] < s.len() &&& 0 <= aug_r[i] < s.len()
                            &&& aug_l[i] != aug_r[i] &&& s[aug_l[i]] as int + s[aug_r[i]] as int == k
                        } by { if i < fin_l.len() as int { assert(aug_l[i] == fin_l[i]); assert(aug_r[i] == fin_r[i]); } };
                        assert forall |i: int| 0 <= i < aug_l.len() implies lo + 1 <= #[trigger] aug_l[i] <= hi - 1 by {
                            if i < fin_l.len() as int { assert(aug_l[i] == fin_l[i]); }
                        };
                        assert forall |i: int| 0 <= i < aug_r.len() implies lo + 1 <= #[trigger] aug_r[i] <= hi - 1 by {
                            if i < fin_r.len() as int { assert(aug_r[i] == fin_r[i]); }
                        };
                        assert(all_indices_distinct(aug_l, aug_r)) by {
                            assert forall |i: int, j: int| 0 <= i < j < aug_l.len() implies aug_l[i] != aug_l[j] by {
                                if j < fin_l.len() as int { assert(aug_l[i] == fin_l[i]); assert(aug_l[j] == fin_l[j]); }
                                else { assert(aug_l[i] == fin_l[i]); assert(aug_l[j] == partner_hi); }
                            };
                            assert forall |i: int, j: int| 0 <= i < j < aug_r.len() implies aug_r[i] != aug_r[j] by {
                                if j < fin_r.len() as int { assert(aug_r[i] == fin_r[i]); assert(aug_r[j] == fin_r[j]); }
                                else { assert(aug_r[i] == fin_r[i]); assert(aug_r[j] == partner_lo); }
                            };
                            assert forall |i: int, j: int| 0 <= i < aug_l.len() && 0 <= j < aug_r.len()
                                implies aug_l[i] != aug_r[j] by {
                                if i < fin_l.len() as int && j < fin_r.len() as int { assert(aug_l[i] == fin_l[i]); assert(aug_r[j] == fin_r[j]); }
                                else if i < fin_l.len() as int { assert(aug_l[i] == fin_l[i]); assert(aug_r[j] == partner_lo); }
                                else if j < fin_r.len() as int { assert(aug_l[i] == partner_hi); assert(aug_r[j] == fin_r[j]); }
                                else { assert(aug_l[i] == partner_hi); assert(aug_r[j] == partner_lo); }
                            };
                        };
                        assert(is_valid_matching(s, aug_l, aug_r, k));
                        lemma_algo_optimal(s, k, lo + 1, hi - 1, aug_l, aug_r);
                    }
                }
            }
        }
    }
}


impl Solution {
    pub open spec fn is_sorted(s: Seq<i32>) -> bool {
        forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn count_occ(s: Seq<i32>, val: i32) -> int
        decreases s.len(),
    {
        if s.len() == 0 { 0 }
        else {
            (if s.last() == val { 1int } else { 0int })
                + Self::count_occ(s.drop_last(), val)
        }
    }

    pub open spec fn is_perm(a: Seq<i32>, b: Seq<i32>) -> bool {
        a.len() == b.len() && forall |v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    proof fn count_occ_nonneg(s: Seq<i32>, val: i32)
        ensures Self::count_occ(s, val) >= 0
        decreases s.len()
    {
        if s.len() > 0 { Self::count_occ_nonneg(s.drop_last(), val); }
    }

    proof fn count_occ_push(s: Seq<i32>, val: i32, query: i32)
        ensures Self::count_occ(s.push(val), query)
            == Self::count_occ(s, query) + if val == query { 1int } else { 0int }
    {
        assert(s.push(val).drop_last() =~= s);
    }

    proof fn count_occ_append(a: Seq<i32>, b: Seq<i32>, val: i32)
        ensures Self::count_occ(a + b, val)
            == Self::count_occ(a, val) + Self::count_occ(b, val)
        decreases b.len()
    {
        if b.len() == 0 {
            assert(a + b =~= a);
        } else {
            assert((a + b).drop_last() =~= a + b.drop_last());
            Self::count_occ_append(a, b.drop_last(), val);
        }
    }

    proof fn count_occ_elem(s: Seq<i32>, idx: int)
        requires 0 <= idx < s.len()
        ensures Self::count_occ(s, s[idx]) >= 1
        decreases s.len()
    {
        Self::count_occ_nonneg(s.drop_last(), s[idx]);
        if idx < s.len() - 1 {
            Self::count_occ_elem(s.drop_last(), idx);
            assert(s.drop_last()[idx] == s[idx]);
        }
    }

    proof fn count_occ_positive_means_present(s: Seq<i32>, val: i32)
        requires Self::count_occ(s, val) >= 1
        ensures exists |i: int| 0 <= i < s.len() && s[i] == val
        decreases s.len()
    {
        if s.len() == 0 { return; }
        if s.last() == val { return; }
        Self::count_occ_positive_means_present(s.drop_last(), val);
        let i = choose |i: int| 0 <= i < s.drop_last().len() && s.drop_last()[i] == val;
        assert(s[i] == val);
    }

    proof fn perm_append(a1: Seq<i32>, a2: Seq<i32>, b1: Seq<i32>, b2: Seq<i32>)
        requires Self::is_perm(a1, b1), Self::is_perm(a2, b2)
        ensures Self::is_perm(a1 + a2, b1 + b2)
    {
        assert forall |v: i32|
            Self::count_occ(a1 + a2, v) == Self::count_occ(b1 + b2, v) by {
            Self::count_occ_append(a1, a2, v);
            Self::count_occ_append(b1, b2, v);
        };
    }

    proof fn perm_preserves_bounds(a: Seq<i32>, b: Seq<i32>, lo: int, hi: int)
        requires
            Self::is_perm(a, b),
            forall |i: int| 0 <= i < b.len() ==> lo <= #[trigger] b[i] as int <= hi,
        ensures
            forall |i: int| 0 <= i < a.len() ==> lo <= #[trigger] a[i] as int <= hi,
    {
        assert forall |i: int| 0 <= i < a.len()
            implies lo <= #[trigger] a[i] as int <= hi by {
            Self::count_occ_elem(a, i);
            Self::count_occ_positive_means_present(b, a[i]);
        };
    }

    fn ms_merge(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
        requires Self::is_sorted(a@), Self::is_sorted(b@)
        ensures
            Self::is_sorted(result@),
            result@.len() == a@.len() + b@.len(),
            Self::is_perm(result@, a@ + b@),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < a.len() || j < b.len()
            invariant
                0 <= i <= a.len(), 0 <= j <= b.len(),
                Self::is_sorted(a@), Self::is_sorted(b@),
                Self::is_sorted(result@),
                result@.len() == i + j,
                Self::is_perm(result@, a@.subrange(0, i as int) + b@.subrange(0, j as int)),
                i < a.len() ==> (forall |k: int| 0 <= k < result@.len() ==> result[k] <= a[i as int]),
                j < b.len() ==> (forall |k: int| 0 <= k < result@.len() ==> result[k] <= b[j as int]),
            decreases a.len() - i + b.len() - j,
        {
            let ghost old_result = result@;
            if i < a.len() && (j >= b.len() || a[i] <= b[j]) {
                result.push(a[i]);
                proof {
                    assert(Self::is_sorted(result@)) by {
                        assert forall |p: int, q: int| 0 <= p <= q < result@.len()
                            implies result[p] <= result[q] by {
                            if q < old_result.len() as int {
                            } else if p < old_result.len() as int {
                                assert(result[q] == a[i as int]);
                            }
                        };
                    };
                    let new_ap = a@.subrange(0, (i + 1) as int);
                    let old_ap = a@.subrange(0, i as int);
                    let bp = b@.subrange(0, j as int);
                    assert(new_ap =~= old_ap.push(a[i as int]));
                    assert(result@ =~= old_result.push(a[i as int]));
                    assert forall |v: i32|
                        Self::count_occ(result@, v)
                        == Self::count_occ(new_ap + bp, v) by {
                        Self::count_occ_push(old_result, a[i as int], v);
                        Self::count_occ_append(new_ap, bp, v);
                        Self::count_occ_push(old_ap, a[i as int], v);
                        Self::count_occ_append(old_ap, bp, v);
                    };
                }
                i = i + 1;
            } else {
                result.push(b[j]);
                proof {
                    assert(Self::is_sorted(result@)) by {
                        assert forall |p: int, q: int| 0 <= p <= q < result@.len()
                            implies result[p] <= result[q] by {
                            if q < old_result.len() as int {
                            } else if p < old_result.len() as int {
                                assert(result[q] == b[j as int]);
                            }
                        };
                    };
                    let ap = a@.subrange(0, i as int);
                    let new_bp = b@.subrange(0, (j + 1) as int);
                    let old_bp = b@.subrange(0, j as int);
                    assert(new_bp =~= old_bp.push(b[j as int]));
                    assert(result@ =~= old_result.push(b[j as int]));
                    assert forall |v: i32|
                        Self::count_occ(result@, v)
                        == Self::count_occ(ap + new_bp, v) by {
                        Self::count_occ_push(old_result, b[j as int], v);
                        Self::count_occ_append(ap, new_bp, v);
                        Self::count_occ_push(old_bp, b[j as int], v);
                        Self::count_occ_append(ap, old_bp, v);
                    };
                }
                j = j + 1;
            }
        }
        proof {
            assert(a@.subrange(0, a@.len() as int) =~= a@);
            assert(b@.subrange(0, b@.len() as int) =~= b@);
        }
        result
    }

    fn ms_sort(input: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            Self::is_sorted(result@),
            Self::is_perm(result@, input@),
        decreases input.len(),
    {
        let n = input.len();
        if n <= 1 {
            let mut result = Vec::new();
            if n == 1 {
                result.push(input[0]);
                proof { assert(result@ =~= input@); }
            } else {
                proof { assert(result@ =~= input@); }
            }
            return result;
        }
        let mid = n / 2;
        let mut left: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < mid
            invariant
                0 <= i <= mid, mid <= n, n == input.len(),
                left.len() == i,
                forall |k: int| 0 <= k < i as int ==> left[k] == input[k],
            decreases mid - i,
        {
            left.push(input[i]);
            i = i + 1;
        }
        let mut right: Vec<i32> = Vec::new();
        let mut j: usize = mid;
        while j < n
            invariant
                mid <= j <= n, n == input.len(),
                right.len() == j - mid,
                forall |k: int| 0 <= k < (j - mid) as int ==> right[k] == input[k + mid as int],
            decreases n - j,
        {
            right.push(input[j]);
            j = j + 1;
        }
        proof {
            assert(left@ =~= input@.subrange(0, mid as int));
            assert(right@ =~= input@.subrange(mid as int, n as int));
            assert(input@ =~= left@ + right@);
        }
        let sorted_left = Self::ms_sort(&left);
        let sorted_right = Self::ms_sort(&right);
        let result = Self::ms_merge(&sorted_left, &sorted_right);
        proof {
            Self::perm_append(sorted_left@, sorted_right@, left@, right@);
            assert forall |v: i32|
                Self::count_occ(result@, v) == Self::count_occ(input@, v) by {
                assert(Self::count_occ(result@, v)
                    == Self::count_occ(sorted_left@ + sorted_right@, v));
                assert(Self::count_occ(sorted_left@ + sorted_right@, v)
                    == Self::count_occ(left@ + right@, v));
                assert(left@ + right@ =~= input@);
            };
        }
        result
    }

    
    pub open spec fn seq_remove(s: Seq<i32>, idx: int) -> Seq<i32> {
        s.subrange(0, idx) + s.subrange(idx + 1, s.len() as int)
    }

    proof fn seq_remove_index(s: Seq<i32>, idx: int, k: int)
        requires 0 <= idx < s.len(), 0 <= k < s.len() - 1
        ensures Self::seq_remove(s, idx)[k]
            == if k < idx { s[k] } else { s[k + 1] }
    {
        let r = Self::seq_remove(s, idx);
        let left = s.subrange(0, idx);
        let right = s.subrange(idx + 1, s.len() as int);
        assert(r =~= left + right);
        if k < idx { assert(r[k] == left[k]); }
        else { assert(r[k] == right[k - idx]); }
    }

    proof fn count_occ_remove(s: Seq<i32>, idx: int, v: i32)
        requires 0 <= idx < s.len()
        ensures Self::count_occ(s, v)
            == Self::count_occ(Self::seq_remove(s, idx), v)
                + if s[idx] == v { 1int } else { 0int }
        decreases s.len()
    {
        let n = s.len();
        if idx == n - 1 {
            assert(Self::seq_remove(s, idx) =~= s.drop_last());
        } else {
            Self::count_occ_remove(s.drop_last(), idx, v);
            let inner = Self::seq_remove(s.drop_last(), idx);
            let full_rem = Self::seq_remove(s, idx);
            assert(full_rem =~= inner.push(s[n - 1]));
            Self::count_occ_push(inner, s[n - 1], v);
        }
    }

    proof fn find_occ_pos(s: Seq<i32>, val: i32) -> (pos: int)
        requires Self::count_occ(s, val) >= 1
        ensures 0 <= pos < s.len(), s[pos] == val
        decreases s.len()
    {
        Self::count_occ_nonneg(s.drop_last(), val);
        if s.last() == val { (s.len() - 1) as int }
        else { Self::find_occ_pos(s.drop_last(), val) }
    }

    proof fn perm_to_bijection(sorted: Seq<i32>, original: Seq<i32>)
        -> (result: (Seq<int>, Seq<int>))
        requires
            sorted.len() == original.len(),
            Self::is_perm(sorted, original),
        ensures ({
            let (perm, inv) = result;
            perm.len() == sorted.len()
            && inv.len() == sorted.len()
            && (forall |k: int| 0 <= k < sorted.len()
                ==> 0 <= #[trigger] perm[k] < sorted.len())
            && (forall |k: int, l: int| 0 <= k < l < sorted.len()
                ==> perm[k] != perm[l])
            && (forall |k: int| 0 <= k < sorted.len()
                ==> sorted[k] == original[#[trigger] perm[k]])
            && (forall |p: int| 0 <= p < sorted.len()
                ==> 0 <= #[trigger] inv[p] < sorted.len())
            && (forall |p: int| 0 <= p < sorted.len()
                ==> perm[#[trigger] inv[p]] == p)
            && (forall |k: int| 0 <= k < sorted.len()
                ==> inv[#[trigger] perm[k]] == k)
        })
        decreases sorted.len()
    {
        let n = sorted.len();
        if n == 0 {
            return (Seq::<int>::empty(), Seq::<int>::empty());
        }

        let val = sorted[n - 1];
        Self::count_occ_nonneg(sorted.drop_last(), val);
        assert(Self::count_occ(sorted, val) >= 1);
        let pos = Self::find_occ_pos(original, val);

        let sorted2 = sorted.drop_last();
        let original2 = Self::seq_remove(original, pos);

        assert forall |v: i32|
            Self::count_occ(sorted2, v) == Self::count_occ(original2, v) by {
            Self::count_occ_remove(original, pos, v);
        };

        let (sub_perm, sub_inv) = Self::perm_to_bijection(sorted2, original2);

        let perm = Seq::new(n as nat, |k: int|
            if k == n - 1 { pos }
            else { let sk = sub_perm[k]; if sk >= pos { sk + 1 } else { sk } }
        );
        let inv = Seq::new(n as nat, |p: int|
            if p == pos { n as int - 1 }
            else { sub_inv[if p > pos { p - 1 } else { p }] }
        );

        assert forall |k: int| 0 <= k < n
            implies 0 <= #[trigger] perm[k] < n by {
            if k != n - 1 { let sk = sub_perm[k]; assert(0 <= sk < n - 1); }
        };

        assert forall |k: int| 0 <= k < n
            implies sorted[k] == original[#[trigger] perm[k]] by {
            if k == n - 1 {
            } else {
                let sk = sub_perm[k];
                assert(sorted2[k] == original2[sk]);
                Self::seq_remove_index(original, pos, sk);
            }
        };

        assert forall |k: int, l: int| 0 <= k < l < n
            implies perm[k] != perm[l] by {
            if l == n - 1 {
                let sk = sub_perm[k]; assert(0 <= sk < n - 1);
            } else if k == n - 1 {
            } else {
                let sk = sub_perm[k]; let sl = sub_perm[l]; assert(sk != sl);
            }
        };

        assert forall |p: int| 0 <= p < n
            implies 0 <= #[trigger] inv[p] < n by {
            if p != pos {
                let up = if p > pos { (p - 1) as int } else { p };
                assert(0 <= up < n - 1);
            }
        };

        assert forall |p: int| 0 <= p < n
            implies perm[#[trigger] inv[p]] == p by {
            if p == pos {
            } else {
                let up = if p > pos { (p - 1) as int } else { p };
                assert(0 <= up < n - 1);
                let si = sub_inv[up];
                assert(sub_perm[si] == up);
                if p > pos {
                    assert(up == p - 1); assert(up >= pos);
                } else {
                    assert(up == p); assert(up < pos);
                }
            }
        };

        assert forall |k: int| 0 <= k < n
            implies inv[#[trigger] perm[k]] == k by {
            if k == n - 1 {
            } else {
                let sk = sub_perm[k];
                let pk = perm[k];
                assert(pk != pos) by {
                    if sk >= pos { assert(pk == sk + 1); }
                    else { assert(pk == sk); }
                };
                let up_pk = if pk > pos { (pk - 1) as int } else { pk };
                assert(up_pk == sk) by {
                    if pk > pos { assert(sk >= pos); assert(pk == sk + 1); }
                    else { assert(sk < pos); assert(pk == sk); }
                };
                assert(inv[pk] == sub_inv[sk]);
            }
        };

        (perm, inv)
    }

    pub fn max_operations(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
            1 <= k <= 1_000_000_000,
        ensures
            0 <= result,
            2 * result as int <= nums.len() as int,
            exists |left_idx: Seq<int>, right_idx: Seq<int>|
                is_valid_matching(nums@, left_idx, right_idx, k as int)
                && left_idx.len() == result as int,
            forall |left_idx: Seq<int>, right_idx: Seq<int>|
                is_valid_matching(nums@, left_idx, right_idx, k as int)
                ==> left_idx.len() <= result as int,
    {
        let ghost original = nums@;
        let nums = Self::ms_sort(&nums);

        proof {
            Self::perm_preserves_bounds(nums@, original, 1, 1_000_000_000);
        }

        let n = nums.len();
        let mut left: i64 = 0;
        let mut right: i64 = n as i64 - 1;
        let mut count: i32 = 0;

        proof {
            max_k_sum_pairs_bound(nums@, k as int, 0, (n - 1) as int);
        }

        while left < right
            invariant
                -1 <= right < n as int,
                0 <= left <= n as int,
                1 <= n <= 100_000,
                n == nums.len(),
                count >= 0,
                2 * count as int <= n as int,
                2 * max_k_sum_pairs(nums@, k as int, 0, n as int - 1) <= n as int,
                forall |i: int| 0 <= i < n ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
                forall |i: int, j: int| 0 <= i <= j < n as int ==> nums[i] <= nums[j],
                count as int + max_k_sum_pairs(nums@, k as int, left as int, right as int)
                    == max_k_sum_pairs(nums@, k as int, 0, n as int - 1),
            decreases dec_val(left as int, right as int),
        {
            let sum = nums[left as usize] + nums[right as usize];
            if sum == k {
                proof {
                    max_k_sum_pairs_bound(nums@, k as int, left as int + 1, right as int - 1);
                }
                count += 1;
                left += 1;
                right -= 1;
            } else if sum < k {
                left += 1;
            } else {
                right -= 1;
            }
        }

        proof {
            let sorted = nums@;

            
            let (perm, inv) = Self::perm_to_bijection(sorted, original);

            
            lemma_algo_achievable(sorted, k as int, 0, (n - 1) as int);
            let gl = matching_left(sorted, k as int, 0, n as int - 1);
            let gr = matching_right(sorted, k as int, 0, n as int - 1);
            assert(gl.len() == count as int);
            assert(is_valid_matching(sorted, gl, gr, k as int));

            
            let orig_gl: Seq<int> = Seq::new(gl.len() as nat, |i: int| perm[gl[i]]);
            let orig_gr: Seq<int> = Seq::new(gr.len() as nat, |i: int| perm[gr[i]]);

            assert forall |i: int| #![trigger orig_gl[i], orig_gr[i]]
                0 <= i < orig_gl.len() implies {
                &&& 0 <= orig_gl[i] < original.len()
                &&& 0 <= orig_gr[i] < original.len()
                &&& orig_gl[i] != orig_gr[i]
                &&& original[orig_gl[i]] as int + original[orig_gr[i]] as int == k as int
            } by {
                let si = gl[i]; let ti = gr[i];
                assert(sorted[si] as int + sorted[ti] as int == k as int);
                assert(original[perm[si]] == sorted[si]);
                assert(original[perm[ti]] == sorted[ti]);
                assert(si != ti);
                if si < ti {} else {}
            };

            assert(all_indices_distinct(orig_gl, orig_gr)) by {
                assert forall |i: int, j: int| 0 <= i < j < orig_gl.len()
                    implies orig_gl[i] != orig_gl[j] by {
                    if gl[i] < gl[j] {} else {}
                };
                assert forall |i: int, j: int| 0 <= i < j < orig_gr.len()
                    implies orig_gr[i] != orig_gr[j] by {
                    if gr[i] < gr[j] {} else {}
                };
                assert forall |i: int, j: int|
                    0 <= i < orig_gl.len() && 0 <= j < orig_gr.len()
                    implies orig_gl[i] != orig_gr[j] by {
                    if gl[i] < gr[j] {} else if gr[j] < gl[i] {} else {
                        assert(gl[i] == gr[j]);
                    }
                };
            };

            assert(is_valid_matching(original, orig_gl, orig_gr, k as int));
            assert(orig_gl.len() == count as int);

            
            assert forall |left_idx: Seq<int>, right_idx: Seq<int>|
                is_valid_matching(original, left_idx, right_idx, k as int)
                implies left_idx.len() <= count as int by {
                let sorted_li: Seq<int> = Seq::new(
                    left_idx.len() as nat, |i: int| inv[left_idx[i]]);
                let sorted_ri: Seq<int> = Seq::new(
                    right_idx.len() as nat, |i: int| inv[right_idx[i]]);

                assert forall |i: int| #![trigger sorted_li[i], sorted_ri[i]]
                    0 <= i < sorted_li.len() implies {
                    &&& 0 <= sorted_li[i] < sorted.len()
                    &&& 0 <= sorted_ri[i] < sorted.len()
                    &&& sorted_li[i] != sorted_ri[i]
                    &&& sorted[sorted_li[i]] as int + sorted[sorted_ri[i]] as int == k as int
                } by {
                    let p = left_idx[i]; let q = right_idx[i];
                    assert(0 <= p < original.len());
                    assert(0 <= q < original.len());
                    assert(perm[inv[p]] == p);
                    assert(sorted[inv[p]] == original[perm[inv[p]]]);
                    assert(perm[inv[q]] == q);
                    assert(sorted[inv[q]] == original[perm[inv[q]]]);
                    assert(p != q);
                    if inv[p] == inv[q] {
                        assert(perm[inv[p]] == perm[inv[q]]);
                        assert(p == q);
                        assert(false);
                    }
                };

                assert(all_indices_distinct(sorted_li, sorted_ri)) by {
                    assert forall |i: int, j: int| 0 <= i < j < sorted_li.len()
                        implies sorted_li[i] != sorted_li[j] by {
                        let p = left_idx[i]; let q = left_idx[j];
                        assert(p != q);
                        if inv[p] == inv[q] {
                            assert(perm[inv[p]] == perm[inv[q]]);
                            assert(false);
                        }
                    };
                    assert forall |i: int, j: int| 0 <= i < j < sorted_ri.len()
                        implies sorted_ri[i] != sorted_ri[j] by {
                        let p = right_idx[i]; let q = right_idx[j];
                        assert(p != q);
                        if inv[p] == inv[q] {
                            assert(perm[inv[p]] == perm[inv[q]]);
                            assert(false);
                        }
                    };
                    assert forall |i: int, j: int|
                        0 <= i < sorted_li.len() && 0 <= j < sorted_ri.len()
                        implies sorted_li[i] != sorted_ri[j] by {
                        let p = left_idx[i]; let q = right_idx[j];
                        assert(p != q);
                        if inv[p] == inv[q] {
                            assert(perm[inv[p]] == perm[inv[q]]);
                            assert(false);
                        }
                    };
                };

                assert(is_valid_matching(sorted, sorted_li, sorted_ri, k as int));

                assert(forall |i: int| 0 <= i < sorted_li.len()
                    ==> 0 <= #[trigger] sorted_li[i] <= n as int - 1);
                assert(forall |i: int| 0 <= i < sorted_ri.len()
                    ==> 0 <= #[trigger] sorted_ri[i] <= n as int - 1);

                lemma_algo_optimal(sorted, k as int, 0, n as int - 1,
                    sorted_li, sorted_ri);
            };
        }

        count
    }
}

}
