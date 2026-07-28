use vstd::prelude::*;
fn main() {}
verus! {

pub struct Solution;

impl Solution {

pub open spec fn is_desc(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] >= s[j]
}

pub open spec fn to_int_seq(s: Seq<i32>) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 { Seq::empty() }
    else { Self::to_int_seq(s.drop_last()).push(s.last() as int) }
}

proof fn lemma_to_int(s: Seq<i32>)
    ensures
        Self::to_int_seq(s).len() == s.len(),
        forall|q: int| 0 <= q < s.len() ==> #[trigger] Self::to_int_seq(s)[q] == s[q] as int,
    decreases s.len()
{
    if s.len() == 0 {} else { Self::lemma_to_int(s.drop_last()); }
}

pub open spec fn insert_desc(s: Seq<int>, v: int) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 { seq![v] }
    else if v >= s[0] { seq![v].add(s) }
    else { seq![s[0]].add(Self::insert_desc(s.subrange(1, s.len() as int), v)) }
}

proof fn lemma_insert_len(s: Seq<int>, v: int)
    ensures Self::insert_desc(s, v).len() == s.len() + 1
    decreases s.len()
{ if s.len() == 0 {} else if v >= s[0] {} else { Self::lemma_insert_len(s.subrange(1, s.len() as int), v); } }

proof fn lemma_insert_pos(s: Seq<int>, v: int, p: int)
    requires
        0 <= p <= s.len(),
        forall|t: int| 0 <= t < p ==> s[t] > v,
        p < s.len() ==> s[p] <= v,
    ensures
        s.insert(p, v) == Self::insert_desc(s, v),
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.insert(0, v) =~= seq![v]);
    } else if v >= s[0] {
        assert(p == 0);
        assert(s.insert(0, v) =~= seq![v].add(s));
    } else {
        assert(p >= 1);
        let sub = s.subrange(1, s.len() as int);
        Self::lemma_insert_pos(sub, v, p - 1);
        assert(s.insert(p, v) =~= seq![s[0]].add(sub.insert(p - 1, v)));
    }
}

proof fn lemma_insert_desc_sorted(s: Seq<int>, v: int)
    requires Self::is_desc(s)
    ensures
        Self::is_desc(Self::insert_desc(s, v)),
        Self::insert_desc(s, v).len() == s.len() + 1,
        forall|w: int| #[trigger] Self::insert_desc(s, v).contains(w) ==> w == v || s.contains(w),
    decreases s.len()
{
    Self::lemma_insert_len(s, v);
    let r = Self::insert_desc(s, v);
    if s.len() == 0 {
    } else if v >= s[0] {
        assert(r =~= seq![v].add(s));
        assert forall|i: int, j: int| 0 <= i <= j < r.len() implies r[i] >= r[j] by {
            if i == 0 { if j == 0 {} else { assert(r[j] == s[j - 1]); assert(s[0] >= s[j - 1]); } }
            else { assert(r[i] == s[i - 1]); assert(r[j] == s[j - 1]); assert(s[i-1] >= s[j-1]); }
        }
    } else {
        let sub = s.subrange(1, s.len() as int);
        Self::lemma_insert_desc_sorted(sub, v);
        Self::lemma_insert_len(sub, v);
        let tail = Self::insert_desc(sub, v);
        assert(r =~= seq![s[0]].add(tail));
        assert forall|i: int, j: int| 0 <= i <= j < r.len() implies r[i] >= r[j] by {
            if i == 0 {
                if j == 0 {} else {
                    assert(r[j] == tail[j - 1]);
                    assert(tail.contains(tail[j - 1]));
                    if tail[j - 1] == v {} else {
                        assert(sub.contains(tail[j - 1]));
                        let c = choose|c: int| 0 <= c < sub.len() && sub[c] == tail[j - 1];
                        assert(sub[c] == s[c + 1]);
                        assert(s[0] >= s[c + 1]);
                    }
                }
            } else { assert(r[i] == tail[i - 1]); assert(r[j] == tail[j - 1]); }
        }
        assert forall|w: int| #[trigger] r.contains(w) implies w == v || s.contains(w) by {
            if w == s[0] { assert(s.contains(s[0])); }
            else {
                assert(tail.contains(w));
                if w == v {} else {
                    assert(sub.contains(w));
                    let c = choose|c: int| 0 <= c < sub.len() && sub[c] == w;
                    assert(s[c + 1] == w); assert(s.contains(w));
                }
            }
        }
    }
}

pub open spec fn ssort(s: Seq<int>) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 { Seq::empty() }
    else { Self::insert_desc(Self::ssort(s.drop_last()), s.last()) }
}

proof fn lemma_ssort_props(s: Seq<int>)
    ensures Self::is_desc(Self::ssort(s)), Self::ssort(s).len() == s.len()
    decreases s.len()
{
    if s.len() == 0 {
        assert(Self::ssort(s) =~= Seq::<int>::empty());
    } else {
        Self::lemma_ssort_props(s.drop_last());
        Self::lemma_insert_desc_sorted(Self::ssort(s.drop_last()), s.last());
        Self::lemma_insert_len(Self::ssort(s.drop_last()), s.last());
    }
}

pub open spec fn merge_ops_n(s: Seq<int>, k: int, n: nat) -> int
    decreases n
{
    if n == 0 { 0 }
    else if s.len() < 2 { 0 }
    else if s[s.len() - 1] >= k { 0 }
    else {
        1 + Self::merge_ops_n(Self::insert_desc(s.subrange(0, s.len() - 2), 2 * s[s.len() - 1] + s[s.len() - 2]), k, (n - 1) as nat)
    }
}

pub open spec fn merge_ops(s: Seq<int>, k: int) -> int {
    Self::merge_ops_n(s, k, s.len())
}


pub fn min_operations(nums: Vec<i32>, k: i32) -> (res: i32)
    requires
        2 <= nums.len() <= 200_000,
        1 <= k <= 1_000_000_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
    ensures
        res as int == Self::merge_ops(Self::ssort(Self::to_int_seq(nums@)), k as int),
{
    let ghost ni = Self::to_int_seq(nums@);
    proof { Self::lemma_to_int(nums@); }

    let mut h: Vec<i64> = Vec::new();
    let ghost mut g: Seq<int> = Seq::empty();
    let mut t: usize = 0;
    while t < nums.len()
        invariant
            0 <= t <= nums.len(),
            2 <= nums.len() <= 200_000,
            1 <= k <= 1_000_000_000,
            ni.len() == nums@.len(),
            forall|q: int| 0 <= q < ni.len() ==> #[trigger] ni[q] == nums@[q] as int,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums@[i] <= 1_000_000_000,
            h@.len() == g.len(),
            forall|q: int| 0 <= q < h@.len() ==> #[trigger] h@[q] as int == g[q],
            g == Self::ssort(ni.subrange(0, t as int)),
            Self::is_desc(g),
            forall|q: int| 0 <= q < g.len() ==> 1 <= #[trigger] g[q] <= 1_000_000_000,
        decreases nums.len() - t,
    {
        let v = nums[t];
        let vi = v as i64;
        assert(ni[t as int] == vi as int);
        let mut p: usize = 0;
        while p < h.len() && h[p] > vi
            invariant
                0 <= p <= h@.len(),
                forall|q: int| 0 <= q < p ==> #[trigger] h@[q] > vi,
                h@.len() == g.len(),
                forall|q: int| 0 <= q < h@.len() ==> #[trigger] h@[q] as int == g[q],
            decreases h@.len() - p,
        {
            p += 1;
        }
        let ghost gold = g;
        proof {
            assert forall|q: int| 0 <= q < p implies g[q] > vi as int by {
                assert(h@[q] > vi);
            }
            if p < g.len() { assert(h@[p as int] <= vi); }
        }
        h.insert(p, vi);
        proof {
            g = gold.insert(p as int, vi as int);
            Self::lemma_insert_pos(gold, vi as int, p as int);
            Self::lemma_insert_desc_sorted(gold, vi as int);
            assert(g == Self::insert_desc(gold, vi as int));
            let pref1 = ni.subrange(0, (t + 1) as int);
            assert(pref1.drop_last() =~= ni.subrange(0, t as int));
            assert(pref1.last() == vi as int);
            assert(Self::ssort(pref1) == Self::insert_desc(Self::ssort(pref1.drop_last()), pref1.last()));
            assert forall|q: int| 0 <= q < h@.len() implies h@[q] as int == g[q] by {}
            assert(1 <= vi <= 1_000_000_000);
        }
        t += 1;
    }
    proof {
        assert(ni.subrange(0, nums.len() as int) =~= ni);
        Self::lemma_ssort_props(ni);
    }

    let ghost gfull = g;
    let mut ops: i32 = 0;
    while h.len() >= 2 && h[h.len() - 1] < k as i64
        invariant
            h@.len() == g.len(),
            forall|q: int| 0 <= q < h@.len() ==> #[trigger] h@[q] as int == g[q],
            Self::is_desc(g),
            0 <= ops,
            nums@.len() <= 200_000,
            h@.len() + ops as int == nums@.len(),
            ops as int <= nums@.len(),
            1 <= k <= 1_000_000_000,
            forall|q: int| 0 <= q < g.len() ==> 1 <= #[trigger] g[q] <= 1_000_000_000 + 2 * (k as int) * (ops as int),
            ops as int + Self::merge_ops(g, k as int) == Self::merge_ops(gfull, k as int),
        decreases h@.len(),
    {
        let ghost gold = g;
        let nh = h.len();
        let x = h[nh - 1];
        let y = h[nh - 2];
        proof {
            assert(g[nh as int - 1] == x as int);
            assert(g[nh as int - 2] == y as int);
            assert(x < k as i64);
            assert(1 <= y <= 1_000_000_000 + 2 * (k as int) * (ops as int));
        }
        assert(ops as int <= 200_000);
        assert(2 * (x as int) + (y as int) <= i64::MAX) by (nonlinear_arith)
            requires x < k as i64, 1 <= k <= 1_000_000_000,
                     y as int <= 1_000_000_000 + 2 * (k as int) * (ops as int),
                     ops as int <= 200_000;
        let merged = 2 * x + y;
        let _ = h.pop();
        let _ = h.pop();
        proof {
            g = gold.subrange(0, gold.len() - 2);
            assert(h@.len() == g.len());
            assert forall|q: int| 0 <= q < h@.len() implies h@[q] as int == g[q] by {}
            assert(Self::is_desc(g));
        }
        let mut p: usize = 0;
        while p < h.len() && h[p] > merged
            invariant
                0 <= p <= h@.len(),
                forall|q: int| 0 <= q < p ==> #[trigger] h@[q] > merged,
                h@.len() == g.len(),
                forall|q: int| 0 <= q < h@.len() ==> #[trigger] h@[q] as int == g[q],
            decreases h@.len() - p,
        {
            p += 1;
        }
        let ghost gmid = g;
        proof {
            assert(forall|q: int| 0 <= q < p ==> g[q] > merged as int);
            assert(p < g.len() ==> g[p as int] <= merged as int);
        }
        h.insert(p, merged);
        proof {
            g = gmid.insert(p as int, merged as int);
            Self::lemma_insert_pos(gmid, merged as int, p as int);
            Self::lemma_insert_desc_sorted(gmid, merged as int);
            assert(merged as int == 2 * gold[gold.len() - 1] + gold[gold.len() - 2]);
            assert(gmid =~= gold.subrange(0, gold.len() - 2));
            assert(g == Self::insert_desc(gold.subrange(0, gold.len() - 2), 2 * gold[gold.len() - 1] + gold[gold.len() - 2]));
            assert(gold.len() >= 2);
            assert(gold[gold.len() - 1] < k as int);
            assert(Self::merge_ops(gold, k as int) == 1 + Self::merge_ops(g, k as int));
            assert forall|q: int| 0 <= q < h@.len() implies h@[q] as int == g[q] by {}
            assert(2 * (k as int) * (ops as int) <= 2 * (k as int) * ((ops + 1) as int)) by (nonlinear_arith)
                requires 1 <= k, 0 <= ops;
            assert(1 <= merged as int);
            assert(merged as int <= 1_000_000_000 + 2 * (k as int) * ((ops + 1) as int)) by (nonlinear_arith)
                requires x < k as i64, 1 <= x, 1 <= k <= 1_000_000_000,
                         y as int <= 1_000_000_000 + 2 * (k as int) * (ops as int),
                         merged as int == 2 * (x as int) + (y as int);
            assert forall|q: int| 0 <= q < g.len() implies 1 <= #[trigger] g[q] <= 1_000_000_000 + 2 * (k as int) * ((ops + 1) as int) by {
                if q == p as int {
                    assert(g[q] == merged as int);
                } else if q < p as int {
                    assert(g[q] == gmid[q]);
                    assert(gmid[q] == gold[q]);
                } else {
                    assert(g[q] == gmid[q - 1]);
                    assert(gmid[q - 1] == gold[q - 1]);
                }
            }
        }
        ops = ops + 1;
    }
    proof {
        if h@.len() < 2 {
            assert(g.len() < 2);
            assert(Self::merge_ops(g, k as int) == 0);
        } else {
            assert(h@[h@.len() - 1] >= k as i64);
            assert(g[g.len() - 1] >= k as int);
            assert(Self::merge_ops(g, k as int) == 0);
        }
    }
    ops
}

}

}
