use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_count_prefix(a: Seq<i32>, v: int, i: int) -> int
        decreases i
    {
        if i <= 0 {
            0
        } else {
            Self::spec_count_prefix(a, v, i - 1) + if a[i - 1] as int == v { 1int } else { 0int }
        }
    }

    pub open spec fn spec_count(a: Seq<i32>, v: int) -> int {
        Self::spec_count_prefix(a, v, a.len() as int)
    }

    pub open spec fn spec_max2(x: int, y: int) -> int {
        if x >= y { x } else { y }
    }

    pub open spec fn spec_max_freq_upto(a: Seq<i32>, upto: int) -> int
        decreases upto
    {
        if upto <= 0 {
            0
        } else {
            Self::spec_max2(Self::spec_max_freq_upto(a, upto - 1), Self::spec_count(a, a[upto - 1] as int))
        }
    }

    pub open spec fn spec_max_freq(a: Seq<i32>) -> int {
        Self::spec_max_freq_upto(a, a.len() as int)
    }

    pub open spec fn spec_min_remaining(a: Seq<i32>) -> int {
        let n = a.len() as int;
        let m = Self::spec_max_freq(a);
        if 2 * m > n { 2 * m - n } else { n % 2 }
    }

    pub open spec fn sorted(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
    }

    // ---------------------------------------------------------------
    // Counting lemmas
    // ---------------------------------------------------------------

    pub proof fn lemma_count_prefix_nonneg(a: Seq<i32>, v: int, i: int)
        requires 0 <= i <= a.len(),
        ensures Self::spec_count_prefix(a, v, i) >= 0,
        decreases i
    {
        if i > 0 {
            Self::lemma_count_prefix_nonneg(a, v, i - 1);
        }
    }

    pub proof fn lemma_count_prefix_eq(a: Seq<i32>, b: Seq<i32>, v: int, i: int)
        requires
            0 <= i <= a.len(),
            0 <= i <= b.len(),
            a.subrange(0, i) =~= b.subrange(0, i),
        ensures
            Self::spec_count_prefix(a, v, i) == Self::spec_count_prefix(b, v, i),
        decreases i
    {
        if i > 0 {
            assert(a.subrange(0, i - 1) =~= b.subrange(0, i - 1));
            Self::lemma_count_prefix_eq(a, b, v, i - 1);
            assert(a[i - 1] == a.subrange(0, i)[i - 1]);
            assert(b[i - 1] == b.subrange(0, i)[i - 1]);
        }
    }

    pub proof fn lemma_count_prefix_concat(s1: Seq<i32>, s2: Seq<i32>, v: int, k: int)
        requires 0 <= k <= s2.len(),
        ensures
            Self::spec_count_prefix(s1 + s2, v, s1.len() as int + k)
                == Self::spec_count(s1, v) + Self::spec_count_prefix(s2, v, k),
        decreases k
    {
        if k == 0 {
            assert((s1 + s2).subrange(0, s1.len() as int) =~= s1);
            Self::lemma_count_prefix_eq(s1 + s2, s1, v, s1.len() as int);
        } else {
            Self::lemma_count_prefix_concat(s1, s2, v, k - 1);
            assert((s1 + s2)[s1.len() as int + k - 1] == s2[k - 1]);
        }
    }

    pub proof fn lemma_count_concat(s1: Seq<i32>, s2: Seq<i32>, v: int)
        ensures Self::spec_count(s1 + s2, v) == Self::spec_count(s1, v) + Self::spec_count(s2, v),
    {
        Self::lemma_count_prefix_concat(s1, s2, v, s2.len() as int);
        assert((s1 + s2).len() == s1.len() + s2.len());
    }

    pub proof fn lemma_count_single(x: i32, v: int)
        ensures Self::spec_count(seq![x], v) == if x as int == v { 1int } else { 0int }
    {
        assert(Self::spec_count(seq![x], v) == Self::spec_count_prefix(seq![x], v, 1));
        assert(Self::spec_count_prefix(seq![x], v, 1) ==
               Self::spec_count_prefix(seq![x], v, 0) + if seq![x][0] as int == v { 1int } else { 0int });
    }

    pub proof fn lemma_count_push(s: Seq<i32>, x: i32, v: int)
        ensures Self::spec_count(s.push(x), v) == Self::spec_count(s, v) + if x as int == v { 1int } else { 0int }
    {
        assert(s.push(x) =~= s + seq![x]);
        Self::lemma_count_concat(s, seq![x], v);
        Self::lemma_count_single(x, v);
    }

    pub proof fn lemma_count_prefix_pos_implies_exists(a: Seq<i32>, v: int, i: int)
        requires 0 <= i <= a.len(), Self::spec_count_prefix(a, v, i) > 0,
        ensures exists|p: int| 0 <= p < i && a[p] as int == v,
        decreases i
    {
        if i > 0 {
            if a[i - 1] as int != v {
                Self::lemma_count_prefix_pos_implies_exists(a, v, i - 1);
            }
        }
    }

    pub proof fn lemma_count_pos_implies_exists(a: Seq<i32>, v: int)
        requires Self::spec_count(a, v) > 0,
        ensures exists|p: int| 0 <= p < a.len() && a[p] as int == v,
    {
        Self::lemma_count_prefix_pos_implies_exists(a, v, a.len() as int);
    }

    pub proof fn lemma_count_prefix_contains(a: Seq<i32>, v: int, i: int, m: int)
        requires 0 <= i < m <= a.len(), a[i] as int == v,
        ensures Self::spec_count_prefix(a, v, m) >= 1,
        decreases m
    {
        if m > i + 1 {
            Self::lemma_count_prefix_contains(a, v, i, m - 1);
        } else {
            Self::lemma_count_prefix_nonneg(a, v, i);
        }
    }

    pub proof fn lemma_self_count_pos(a: Seq<i32>, i: int)
        requires 0 <= i < a.len(),
        ensures Self::spec_count(a, a[i] as int) >= 1,
    {
        Self::lemma_count_prefix_contains(a, a[i] as int, i, a.len() as int);
    }

    pub proof fn lemma_count_prefix_via_equiv(u: Seq<i32>, w: Seq<i32>, k: int, m: int)
        requires
            u.len() == w.len(),
            0 <= k < u.len(),
            0 <= m <= u.len(),
            forall|i: int, j: int| 0 <= i < u.len() && 0 <= j < u.len() ==> (u[i] == u[j] <==> w[i] == w[j]),
        ensures
            Self::spec_count_prefix(u, u[k] as int, m) == Self::spec_count_prefix(w, w[k] as int, m),
        decreases m
    {
        if m > 0 {
            Self::lemma_count_prefix_via_equiv(u, w, k, m - 1);
            assert(u[m - 1] == u[k] <==> w[m - 1] == w[k]);
        }
    }

    pub proof fn lemma_count_via_equiv(u: Seq<i32>, w: Seq<i32>, k: int)
        requires
            u.len() == w.len(),
            0 <= k < u.len(),
            forall|i: int, j: int| 0 <= i < u.len() && 0 <= j < u.len() ==> (u[i] == u[j] <==> w[i] == w[j]),
        ensures
            Self::spec_count(u, u[k] as int) == Self::spec_count(w, w[k] as int),
    {
        Self::lemma_count_prefix_via_equiv(u, w, k, u.len() as int);
    }

    // ---------------------------------------------------------------
    // Verified merge sort (needed because element values can be as large
    // as 10^9, so they can't be used directly as array indices; sorting
    // lets us assign each distinct value a dense rank in [1, n] instead).
    // ---------------------------------------------------------------

    pub proof fn lemma_sorted_push(s: Seq<i32>, x: i32)
        requires
            Self::sorted(s),
            s.len() > 0 ==> s[s.len() as int - 1] <= x,
        ensures
            Self::sorted(s.push(x)),
    {
        assert forall|i: int, j: int| 0 <= i < j < s.push(x).len() implies
            s.push(x)[i] <= s.push(x)[j] by {
            if j < s.len() {
                assert(s.push(x)[i] == s[i]);
                assert(s.push(x)[j] == s[j]);
            } else {
                if i < s.len() {
                    assert(s.push(x)[i] == s[i]);
                    assert(s[i] <= s[s.len() as int - 1] || i == s.len() as int - 1);
                }
            }
        }
    }

    fn merge(left: Vec<i32>, right: Vec<i32>) -> (result: Vec<i32>)
        requires
            Self::sorted(left@),
            Self::sorted(right@),
        ensures
            Self::sorted(result@),
            result.len() == left.len() + right.len(),
            forall|v: int| Self::spec_count(result@, v) == Self::spec_count(left@, v) + Self::spec_count(right@, v),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < left.len() && j < right.len()
            invariant
                0 <= i <= left.len(),
                0 <= j <= right.len(),
                Self::sorted(left@),
                Self::sorted(right@),
                Self::sorted(result@),
                result.len() == i + j,
                forall|v: int| Self::spec_count(result@, v) ==
                    Self::spec_count(left@.subrange(0, i as int), v) + Self::spec_count(right@.subrange(0, j as int), v),
                result.len() > 0 && i < left.len() ==> result[result.len() as int - 1] <= left[i as int],
                result.len() > 0 && j < right.len() ==> result[result.len() as int - 1] <= right[j as int],
            decreases (left.len() - i) as int + (right.len() - j) as int
        {
            let ghost old_result = result@;
            if left[i] <= right[j] {
                let x = left[i];
                proof {
                    assert(left@.subrange(0, i as int + 1) =~= left@.subrange(0, i as int).push(x));
                    assert forall|v: int| Self::spec_count(left@.subrange(0, i as int + 1), v) ==
                        Self::spec_count(left@.subrange(0, i as int), v) + if x as int == v { 1int } else { 0int } by {
                        Self::lemma_count_push(left@.subrange(0, i as int), x, v);
                    }
                    Self::lemma_sorted_push(result@, x);
                }
                result.push(x);
                i += 1;
                proof {
                    assert(result@ =~= old_result.push(x));
                    assert forall|v: int| Self::spec_count(result@, v) ==
                        Self::spec_count(left@.subrange(0, i as int), v) + Self::spec_count(right@.subrange(0, j as int), v) by {
                        Self::lemma_count_push(old_result, x, v);
                    }
                }
            } else {
                let x = right[j];
                proof {
                    assert(right@.subrange(0, j as int + 1) =~= right@.subrange(0, j as int).push(x));
                    assert forall|v: int| Self::spec_count(right@.subrange(0, j as int + 1), v) ==
                        Self::spec_count(right@.subrange(0, j as int), v) + if x as int == v { 1int } else { 0int } by {
                        Self::lemma_count_push(right@.subrange(0, j as int), x, v);
                    }
                    Self::lemma_sorted_push(result@, x);
                }
                result.push(x);
                j += 1;
                proof {
                    assert(result@ =~= old_result.push(x));
                    assert forall|v: int| Self::spec_count(result@, v) ==
                        Self::spec_count(left@.subrange(0, i as int), v) + Self::spec_count(right@.subrange(0, j as int), v) by {
                        Self::lemma_count_push(old_result, x, v);
                    }
                }
            }
        }
        while i < left.len()
            invariant
                0 <= i <= left.len(),
                0 <= j <= right.len(),
                i == left.len() || j == right.len(),
                Self::sorted(left@),
                Self::sorted(result@),
                result.len() == i + j,
                forall|v: int| Self::spec_count(result@, v) ==
                    Self::spec_count(left@.subrange(0, i as int), v) + Self::spec_count(right@.subrange(0, j as int), v),
                result.len() > 0 && i < left.len() ==> result[result.len() as int - 1] <= left[i as int],
                result.len() > 0 && j < right.len() ==> result[result.len() as int - 1] <= right[j as int],
            decreases left.len() - i
        {
            let ghost old_result = result@;
            let x = left[i];
            proof {
                assert(left@.subrange(0, i as int + 1) =~= left@.subrange(0, i as int).push(x));
                assert forall|v: int| Self::spec_count(left@.subrange(0, i as int + 1), v) ==
                    Self::spec_count(left@.subrange(0, i as int), v) + if x as int == v { 1int } else { 0int } by {
                    Self::lemma_count_push(left@.subrange(0, i as int), x, v);
                }
                Self::lemma_sorted_push(result@, x);
            }
            result.push(x);
            i += 1;
            proof {
                assert(result@ =~= old_result.push(x));
                assert forall|v: int| Self::spec_count(result@, v) ==
                    Self::spec_count(left@.subrange(0, i as int), v) + Self::spec_count(right@.subrange(0, j as int), v) by {
                    Self::lemma_count_push(old_result, x, v);
                }
            }
        }
        while j < right.len()
            invariant
                0 <= i <= left.len(),
                0 <= j <= right.len(),
                Self::sorted(right@),
                Self::sorted(result@),
                result.len() == i + j,
                forall|v: int| Self::spec_count(result@, v) ==
                    Self::spec_count(left@.subrange(0, i as int), v) + Self::spec_count(right@.subrange(0, j as int), v),
                result.len() > 0 && j < right.len() ==> result[result.len() as int - 1] <= right[j as int],
            decreases right.len() - j
        {
            let ghost old_result = result@;
            let x = right[j];
            proof {
                assert(right@.subrange(0, j as int + 1) =~= right@.subrange(0, j as int).push(x));
                assert forall|v: int| Self::spec_count(right@.subrange(0, j as int + 1), v) ==
                    Self::spec_count(right@.subrange(0, j as int), v) + if x as int == v { 1int } else { 0int } by {
                    Self::lemma_count_push(right@.subrange(0, j as int), x, v);
                }
                Self::lemma_sorted_push(result@, x);
            }
            result.push(x);
            j += 1;
            proof {
                assert(result@ =~= old_result.push(x));
                assert forall|v: int| Self::spec_count(result@, v) ==
                    Self::spec_count(left@.subrange(0, i as int), v) + Self::spec_count(right@.subrange(0, j as int), v) by {
                    Self::lemma_count_push(old_result, x, v);
                }
            }
        }
        proof {
            assert(left@.subrange(0, left.len() as int) =~= left@);
            assert(right@.subrange(0, right.len() as int) =~= right@);
        }
        result
    }

    fn merge_sort(a: Vec<i32>) -> (result: Vec<i32>)
        ensures
            Self::sorted(result@),
            result.len() == a.len(),
            forall|v: int| Self::spec_count(result@, v) == Self::spec_count(a@, v),
        decreases a.len()
    {
        let n = a.len();
        if n <= 1 {
            a
        } else {
            let mid = n / 2;
            let mut left: Vec<i32> = Vec::new();
            let mut k: usize = 0;
            while k < mid
                invariant
                    0 <= k <= mid,
                    mid <= n,
                    n == a.len(),
                    left.len() == k,
                    forall|t: int| 0 <= t < k ==> left[t] == a[t],
                decreases mid - k
            {
                left.push(a[k]);
                k += 1;
            }
            let mut right: Vec<i32> = Vec::new();
            let mut k2: usize = mid;
            while k2 < n
                invariant
                    mid <= k2 <= n,
                    n == a.len(),
                    right.len() == k2 - mid,
                    forall|t: int| 0 <= t < k2 - mid ==> right[t] == a[mid as int + t],
                decreases n - k2
            {
                right.push(a[k2]);
                k2 += 1;
            }
            proof {
                assert(left@ =~= a@.subrange(0, mid as int));
                assert(right@ =~= a@.subrange(mid as int, n as int));
                assert(a@ =~= left@ + right@);
            }
            let left_sorted = Self::merge_sort(left);
            let right_sorted = Self::merge_sort(right);
            let result = Self::merge(left_sorted, right_sorted);
            proof {
                assert forall|v: int| Self::spec_count(result@, v) == Self::spec_count(a@, v) by {
                    Self::lemma_count_concat(left@, right@, v);
                }
            }
            result
        }
    }

    // ---------------------------------------------------------------
    // Dense rank over a sorted array, and binary search to look a
    // value's rank up.
    // ---------------------------------------------------------------

    pub proof fn lemma_rank_reflects(s: Seq<i32>, rank: Seq<i32>, p: int, q: int)
        requires
            Self::sorted(s),
            s.len() == rank.len(),
            rank.len() > 0,
            rank[0] == 1,
            forall|t: int| 0 < t < rank.len() ==> #[trigger] rank[t] == rank[t - 1] + if s[t] > s[t - 1] { 1int } else { 0int },
            0 <= p <= q < s.len(),
        ensures
            rank[p] <= rank[q],
            s[p] == s[q] <==> rank[p] == rank[q],
        decreases q - p
    {
        if p == q {
        } else if q == p + 1 {
            assert(s[p] <= s[q]);
        } else {
            Self::lemma_rank_reflects(s, rank, p, p + 1);
            Self::lemma_rank_reflects(s, rank, p + 1, q);
            assert(s[p] <= s[p + 1]);
            assert(s[p + 1] <= s[q]);
        }
    }

    pub proof fn lemma_rank_reflects_sym(s: Seq<i32>, rank: Seq<i32>, p: int, q: int)
        requires
            Self::sorted(s),
            s.len() == rank.len(),
            rank.len() > 0,
            rank[0] == 1,
            forall|t: int| 0 < t < rank.len() ==> #[trigger] rank[t] == rank[t - 1] + if s[t] > s[t - 1] { 1int } else { 0int },
            0 <= p < s.len(),
            0 <= q < s.len(),
        ensures
            s[p] == s[q] <==> rank[p] == rank[q],
    {
        if p <= q {
            Self::lemma_rank_reflects(s, rank, p, q);
        } else {
            Self::lemma_rank_reflects(s, rank, q, p);
        }
    }

    fn compute_rank(s: &Vec<i32>) -> (rank: Vec<i32>)
        requires
            Self::sorted(s@),
            s.len() >= 1,
            s.len() <= 200000,
        ensures
            rank.len() == s.len(),
            rank[0] == 1,
            forall|t: int| 0 < t < rank.len() ==> #[trigger] rank[t] == rank[t - 1] + if s[t] > s[t - 1] { 1int } else { 0int },
            forall|t: int| 0 <= t < rank.len() ==> 1 <= #[trigger] rank[t] <= t + 1,
    {
        let n = s.len();
        let mut rank: Vec<i32> = Vec::new();
        rank.push(1);
        let mut k: usize = 1;
        while k < n
            invariant
                1 <= k <= n,
                n == s.len(),
                n <= 200000,
                rank.len() == k,
                rank[0] == 1,
                forall|t: int| 0 < t < k ==> #[trigger] rank[t] == rank[t - 1] + if s[t] > s[t - 1] { 1int } else { 0int },
                forall|t: int| 0 <= t < k ==> 1 <= #[trigger] rank[t] <= t + 1,
            decreases n - k
        {
            let inc: i32 = if s[k] > s[k - 1] { 1 } else { 0 };
            assert(1 <= rank[k as int - 1] <= k as int);
            assert(k <= n);
            assert(n <= 200000);
            assert(rank[k as int - 1] as int + inc as int <= 200001);
            let newval = rank[k - 1] + inc;
            let ghost old_rank = rank@;
            rank.push(newval);
            proof {
                assert(rank@ =~= old_rank.push(newval));
            }
            k += 1;
        }
        rank
    }

    fn find_index(s: &Vec<i32>, x: i32) -> (pos: usize)
        requires
            Self::sorted(s@),
            Self::spec_count(s@, x as int) > 0,
        ensures
            pos < s.len(),
            s[pos as int] == x,
    {
        proof {
            Self::lemma_count_pos_implies_exists(s@, x as int);
        }
        let mut lo: usize = 0;
        let mut hi: usize = s.len();
        while lo < hi
            invariant
                hi <= s.len(),
                lo <= hi,
                Self::sorted(s@),
                exists|p: int| lo <= p < hi && s[p] == x,
            decreases hi - lo
        {
            let mid = lo + (hi - lo) / 2;
            if s[mid] < x {
                proof {
                    let p0 = choose|p: int| lo <= p && p < hi && s[p] == x;
                    if p0 <= mid as int {
                        if p0 < mid as int {
                            assert(s[p0] <= s[mid as int]);
                        }
                        assert(false);
                    }
                    assert(mid as int + 1 <= p0 < hi as int && s[p0] == x);
                }
                lo = mid + 1;
            } else if s[mid] > x {
                proof {
                    let p0 = choose|p: int| lo <= p && p < hi && s[p] == x;
                    if p0 >= mid as int {
                        if p0 > mid as int {
                            assert(s[mid as int] <= s[p0]);
                        }
                        assert(false);
                    }
                    assert(lo as int <= p0 < mid as int && s[p0] == x);
                }
                hi = mid;
            } else {
                return mid;
            }
        }
        assert(false);
        0
    }

    // ---------------------------------------------------------------
    // Coordinate compression: remaps each element of `a` to its dense
    // rank among distinct values, landing every element in [1, a.len()]
    // while exactly preserving per-index occurrence counts.
    // ---------------------------------------------------------------

    fn compress(a: &Vec<i32>) -> (comp: Vec<i32>)
        requires
            a.len() >= 1,
            a.len() <= 200000,
        ensures
            comp.len() == a.len(),
            forall|t: int| 0 <= t < comp.len() ==> 1 <= #[trigger] comp[t] <= a.len(),
            forall|k: int| 0 <= k < a.len() ==> Self::spec_count(comp@, comp[k] as int) == Self::spec_count(a@, a[k] as int),
    {
        let mut a_copy: Vec<i32> = Vec::new();
        let mut ci: usize = 0;
        while ci < a.len()
            invariant
                0 <= ci <= a.len(),
                a_copy.len() == ci,
                forall|t: int| 0 <= t < ci ==> a_copy[t] == a[t],
            decreases a.len() - ci
        {
            a_copy.push(a[ci]);
            ci += 1;
        }
        proof {
            assert(a_copy@ =~= a@);
        }
        let s = Self::merge_sort(a_copy);
        let rank = Self::compute_rank(&s);
        let n = a.len();
        let mut comp: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let ghost mut pos_seq: Seq<int> = Seq::empty();
        while i < n
            invariant
                0 <= i <= n,
                n == a.len(),
                comp.len() == i,
                s.len() == a.len(),
                Self::sorted(s@),
                rank.len() == s.len(),
                rank.len() > 0,
                rank[0] == 1,
                forall|t: int| 0 < t < rank.len() ==> #[trigger] rank[t] == rank[t - 1] + if s[t] > s[t - 1] { 1int } else { 0int },
                forall|t: int| 0 <= t < rank.len() ==> 1 <= #[trigger] rank[t] <= t + 1,
                forall|v: int| Self::spec_count(s@, v) == Self::spec_count(a@, v),
                pos_seq.len() == i,
                forall|t: int| 0 <= t < i ==> 0 <= #[trigger] pos_seq[t] < s.len(),
                forall|t: int| 0 <= t < i ==> s[pos_seq[t]] == a[t],
                forall|t: int| 0 <= t < i ==> rank[pos_seq[t]] == comp[t],
            decreases n - i
        {
            proof {
                Self::lemma_self_count_pos(a@, i as int);
                assert(Self::spec_count(s@, a[i as int] as int) >= 1);
            }
            let pos = Self::find_index(&s, a[i]);
            let r = rank[pos];
            comp.push(r);
            proof {
                pos_seq = pos_seq.push(pos as int);
            }
            i += 1;
        }
        proof {
            assert forall|ii: int, jj: int| 0 <= ii < a.len() as int && 0 <= jj < a.len() as int implies
                (a[ii] == a[jj] <==> comp[ii] == comp[jj]) by {
                Self::lemma_rank_reflects_sym(s@, rank@, pos_seq[ii], pos_seq[jj]);
            }
            assert forall|k: int| 0 <= k < a.len() as int implies
                Self::spec_count(comp@, comp[k] as int) == Self::spec_count(a@, a[k] as int) by {
                Self::lemma_count_via_equiv(a@, comp@, k);
            }
        }
        comp
    }

    // ---------------------------------------------------------------
    // Bridge between "max frequency by scanning candidate values 1..n"
    // (what the counting-array algorithm below computes) and
    // "max frequency by scanning indices" (the domain-independent
    // spec_max_freq used in the contract).
    // ---------------------------------------------------------------

    pub open spec fn spec_max_freq_by_value_upto(w: Seq<i32>, upto: int) -> int
        decreases upto
    {
        if upto <= 0 {
            0
        } else {
            Self::spec_max2(Self::spec_max_freq_by_value_upto(w, upto - 1), Self::spec_count(w, upto))
        }
    }

    pub proof fn lemma_value_max_is_upper_bound(w: Seq<i32>, upto: int, v: int)
        requires 1 <= v <= upto,
        ensures Self::spec_max_freq_by_value_upto(w, upto) >= Self::spec_count(w, v),
        decreases upto
    {
        if v != upto {
            Self::lemma_value_max_is_upper_bound(w, upto - 1, v);
        }
    }

    pub proof fn lemma_value_max_nonneg(w: Seq<i32>, upto: int)
        ensures Self::spec_max_freq_by_value_upto(w, upto) >= 0,
        decreases upto
    {
        if upto > 0 {
            Self::lemma_value_max_nonneg(w, upto - 1);
        }
    }

    pub proof fn lemma_index_max_nonneg(w: Seq<i32>, upto: int)
        requires 0 <= upto <= w.len(),
        ensures Self::spec_max_freq_upto(w, upto) >= 0,
        decreases upto
    {
        if upto > 0 {
            Self::lemma_index_max_nonneg(w, upto - 1);
            Self::lemma_count_prefix_nonneg(w, w[upto - 1] as int, w.len() as int);
        }
    }

    pub proof fn lemma_index_max_is_upper_bound(w: Seq<i32>, upto: int, i: int)
        requires 0 <= i < upto <= w.len(),
        ensures Self::spec_max_freq_upto(w, upto) >= Self::spec_count(w, w[i] as int),
        decreases upto
    {
        if i != upto - 1 {
            Self::lemma_index_max_is_upper_bound(w, upto - 1, i);
        }
    }

    pub proof fn lemma_value_le_index_max(w: Seq<i32>, big_bound: int, bound: int, idx_upto: int)
        requires
            0 <= bound <= big_bound,
            idx_upto == w.len(),
            forall|i: int| 0 <= i < w.len() ==> 1 <= w[i] && w[i] as int <= big_bound,
        ensures
            Self::spec_max_freq_by_value_upto(w, bound) <= Self::spec_max_freq_upto(w, idx_upto),
        decreases bound
    {
        Self::lemma_index_max_nonneg(w, idx_upto);
        if bound > 0 {
            Self::lemma_value_le_index_max(w, big_bound, bound - 1, idx_upto);
            if Self::spec_count(w, bound) > 0 {
                Self::lemma_count_pos_implies_exists(w, bound);
                let i0 = choose|i: int| 0 <= i < w.len() && w[i] as int == bound;
                Self::lemma_index_max_is_upper_bound(w, idx_upto, i0);
                assert(Self::spec_count(w, w[i0] as int) == Self::spec_count(w, bound));
                assert(Self::spec_max_freq_upto(w, idx_upto) >= Self::spec_count(w, bound));
            } else {
                Self::lemma_index_max_nonneg(w, idx_upto);
                assert(Self::spec_max_freq_upto(w, idx_upto) >= Self::spec_count(w, bound));
            }
            assert(Self::spec_max_freq_by_value_upto(w, bound) ==
                Self::spec_max2(Self::spec_max_freq_by_value_upto(w, bound - 1), Self::spec_count(w, bound)));
            if Self::spec_max_freq_by_value_upto(w, bound - 1) >= Self::spec_count(w, bound) {
                assert(Self::spec_max2(Self::spec_max_freq_by_value_upto(w, bound - 1), Self::spec_count(w, bound))
                    == Self::spec_max_freq_by_value_upto(w, bound - 1));
            } else {
                assert(Self::spec_max2(Self::spec_max_freq_by_value_upto(w, bound - 1), Self::spec_count(w, bound))
                    == Self::spec_count(w, bound));
            }
            assert(Self::spec_max_freq_by_value_upto(w, bound) <= Self::spec_max_freq_upto(w, idx_upto));
        }
    }

    pub proof fn lemma_index_max_le_by_pointwise(w: Seq<i32>, upto: int, bound_val: int)
        requires
            0 <= upto <= w.len(),
            bound_val >= 0,
            forall|i: int| 0 <= i < upto ==> Self::spec_count(w, w[i] as int) <= bound_val,
        ensures Self::spec_max_freq_upto(w, upto) <= bound_val,
        decreases upto
    {
        if upto > 0 {
            Self::lemma_index_max_le_by_pointwise(w, upto - 1, bound_val);
        }
    }

    pub proof fn lemma_value_index_max_eq(w: Seq<i32>, bound: int)
        requires
            bound == w.len(),
            forall|i: int| 0 <= i < w.len() ==> 1 <= w[i] && w[i] as int <= bound,
        ensures
            Self::spec_max_freq_by_value_upto(w, bound) == Self::spec_max_freq_upto(w, w.len() as int),
    {
        Self::lemma_value_le_index_max(w, bound, bound, w.len() as int);
        assert forall|i: int| 0 <= i < w.len() implies
            Self::spec_count(w, w[i] as int) <= Self::spec_max_freq_by_value_upto(w, bound) by {
            Self::lemma_value_max_is_upper_bound(w, bound, w[i] as int);
        }
        Self::lemma_value_max_nonneg(w, bound);
        Self::lemma_index_max_le_by_pointwise(w, w.len() as int, Self::spec_max_freq_by_value_upto(w, bound));
    }

    // Two sequences with the same per-index count sequence have the same index-based max.
    pub proof fn lemma_index_max_pointwise_eq(u: Seq<i32>, w: Seq<i32>, upto: int)
        requires
            0 <= upto <= u.len(),
            u.len() == w.len(),
            forall|i: int| 0 <= i < upto ==> Self::spec_count(u, u[i] as int) == Self::spec_count(w, w[i] as int),
        ensures
            Self::spec_max_freq_upto(u, upto) == Self::spec_max_freq_upto(w, upto),
        decreases upto
    {
        if upto > 0 {
            Self::lemma_index_max_pointwise_eq(u, w, upto - 1);
        }
    }

    // ---------------------------------------------------------------
    // Main function
    // ---------------------------------------------------------------

    pub fn min_remaining_after_epic_transformation(a: Vec<i32>) -> (res: i32)
        requires
            1 <= a.len() <= 200000,
            forall|j: int| 0 <= j < a.len() as int ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
        ensures
            res as int == Self::spec_min_remaining(a@),
    {
        let n: usize = a.len();
        let comp = Self::compress(&a);

        let mut cnt: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= n
            invariant
                n == a.len(),
                1 <= n <= 200000,
                0 <= k <= n + 1,
                cnt.len() == k,
                forall|j: int| 0 <= j < k as int ==> cnt[j] == 0,
            decreases n + 1 - k,
        {
            cnt.push(0);
            k = k + 1;
        }

        let mut i: usize = 0;
        while i < n
            invariant
                n == a.len(),
                1 <= n <= 200000,
                cnt.len() == n + 1,
                0 <= i <= n,
                cnt[0] == 0,
                comp.len() == a.len(),
                forall|t: int| 0 <= t < comp.len() ==> 1 <= #[trigger] comp[t] <= a.len(),
                forall|v: int| 1 <= v <= n as int ==> cnt[v] as int == Self::spec_count_prefix(comp@, v, i as int),
                forall|v: int| 1 <= v <= n as int ==> 0 <= #[trigger] cnt[v] <= i as i32,
            decreases n - i,
        {
            let v: usize = comp[i] as usize;
            assert(0 <= cnt[v as int] <= i as i32);
            assert(i <= 199999);
            assert(cnt[v as int] + 1 <= 200000);
            let ghost old_cnt = cnt@;
            cnt.set(v, cnt[v] + 1);
            proof {
                assert(v as int == comp[i as int] as int);
                assert(1 <= v as int <= n as int);
                assert forall|vv: int| 1 <= vv <= n as int implies cnt[vv] as int == Self::spec_count_prefix(comp@, vv, i as int + 1) by {
                    if vv == v as int {
                        assert(cnt[vv] == old_cnt[vv] + 1);
                        assert(old_cnt[vv] as int == Self::spec_count_prefix(comp@, vv, i as int));
                        assert(comp[i as int] as int == vv);
                    } else {
                        assert(cnt[vv] == old_cnt[vv]);
                        assert(old_cnt[vv] as int == Self::spec_count_prefix(comp@, vv, i as int));
                        assert(comp[i as int] as int != vv);
                    }
                };
                assert forall|vv: int| 1 <= vv <= n as int implies 0 <= #[trigger] cnt[vv] <= i as i32 + 1 by {
                    if vv == v as int {
                        assert(0 <= old_cnt[vv] <= i as i32);
                        assert(cnt[vv] == old_cnt[vv] + 1);
                    } else {
                        assert(cnt[vv] == old_cnt[vv]);
                    }
                };
                assert(cnt[0] == 0);
            }
            i = i + 1;
        }

        let mut mx: i32 = 0;
        let mut p: usize = 1;
        while p <= n
            invariant
                n == a.len(),
                1 <= n <= 200000,
                cnt.len() == n + 1,
                cnt[0] == 0,
                comp.len() == a.len(),
                forall|t: int| 0 <= t < comp.len() ==> 1 <= #[trigger] comp[t] <= a.len(),
                forall|v: int| 1 <= v <= n as int ==> cnt[v] as int == Self::spec_count(comp@, v),
                forall|v: int| 1 <= v <= n as int ==> 0 <= #[trigger] cnt[v] <= n as i32,
                1 <= p <= n + 1,
                0 <= mx as int <= n as int,
                mx as int == Self::spec_max_freq_by_value_upto(comp@, p as int - 1),
            decreases n + 1 - p,
        {
            if cnt[p] > mx {
                assert(0 <= cnt[p as int] <= n as i32);
                mx = cnt[p];
            }
            proof {
                assert(cnt[p as int] as int == Self::spec_count(comp@, p as int));
                assert(mx as int == Self::spec_max2(Self::spec_max_freq_by_value_upto(comp@, p as int - 1), Self::spec_count(comp@, p as int)));
                assert(Self::spec_max_freq_by_value_upto(comp@, p as int) == Self::spec_max2(Self::spec_max_freq_by_value_upto(comp@, p as int - 1), Self::spec_count(comp@, p as int)));
            }
            p = p + 1;
        }

        proof {
            assert(mx as int == Self::spec_max_freq_by_value_upto(comp@, n as int));
            Self::lemma_value_index_max_eq(comp@, n as int);
            assert(Self::spec_max_freq_by_value_upto(comp@, n as int) == Self::spec_max_freq_upto(comp@, comp.len() as int));
            assert(Self::spec_max_freq(comp@) == Self::spec_max_freq_upto(comp@, comp.len() as int));
            Self::lemma_index_max_pointwise_eq(comp@, a@, n as int);
            assert(Self::spec_max_freq_upto(comp@, n as int) == Self::spec_max_freq_upto(a@, n as int));
            assert(Self::spec_max_freq(a@) == Self::spec_max_freq_upto(a@, a.len() as int));
            assert(mx as int == Self::spec_max_freq(a@));
        }

        let n_i32: i32 = n as i32;
        let two_mx: i32 = mx + mx;
        if two_mx > n_i32 {
            proof {
                assert(two_mx as int == 2 * Self::spec_max_freq(a@));
                assert(n_i32 as int == a.len() as int);
                assert(2 * Self::spec_max_freq(a@) > a.len() as int);
                assert(Self::spec_min_remaining(a@) == 2 * Self::spec_max_freq(a@) - a.len() as int);
            }
            two_mx - n_i32
        } else {
            proof {
                assert(two_mx as int == 2 * Self::spec_max_freq(a@));
                assert(n_i32 as int == a.len() as int);
                assert(!(2 * Self::spec_max_freq(a@) > a.len() as int));
                assert(Self::spec_min_remaining(a@) == a.len() as int % 2);
            }
            n_i32 % 2
        }
    }
}

}
