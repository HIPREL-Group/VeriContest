use vstd::prelude::*;
use vstd::seq_lib::lemma_seq_concat_contains_all_elements;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn best_in_prefix(nums: Seq<i32>, marked: Seq<bool>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            nums.len() as int
        } else {
            let prev = Self::best_in_prefix(nums, marked, end - 1);
            let j = end - 1;
            if marked[j] {
                prev
            } else if prev == nums.len() as int || nums[j] < nums[prev] || (nums[j] == nums[prev] && j < prev) {
                j
            } else {
                prev
            }
        }
    }

    pub open spec fn best_unmarked(nums: Seq<i32>, marked: Seq<bool>) -> int {
        Self::best_in_prefix(nums, marked, nums.len() as int)
    }

    pub open spec fn sum_unmarked_prefix(nums: Seq<i32>, marked: Seq<bool>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::sum_unmarked_prefix(nums, marked, end - 1)
                + if marked[end - 1] { 0 } else { nums[end - 1] as int }
        }
    }

    pub open spec fn sum_unmarked(nums: Seq<i32>, marked: Seq<bool>) -> int {
        Self::sum_unmarked_prefix(nums, marked, nums.len() as int)
    }

    pub open spec fn all_unmarked(n: int) -> Seq<bool>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else {
            Self::all_unmarked(n - 1).push(false)
        }
    }

    pub open spec fn mark_index(marked: Seq<bool>, idx: int) -> Seq<bool> {
        if marked[idx] {
            marked
        } else {
            marked.update(idx, true)
        }
    }

    pub open spec fn mark_steps(nums: Seq<i32>, marked: Seq<bool>, steps: int) -> Seq<bool>
        decreases steps,
    {
        if steps <= 0 {
            marked
        } else {
            let prev = Self::mark_steps(nums, marked, steps - 1);
            let b = Self::best_unmarked(nums, prev);
            if b == nums.len() as int {
                prev
            } else {
                prev.update(b, true)
            }
        }
    }

    pub open spec fn apply_query(nums: Seq<i32>, marked: Seq<bool>, query: Vec<i32>) -> Seq<bool> {
        let marked1 = Self::mark_index(marked, query[0] as int);
        Self::mark_steps(nums, marked1, query[1] as int)
    }

    pub open spec fn state_after(nums: Seq<i32>, queries: Seq<Vec<i32>>, t: int) -> Seq<bool>
        decreases t,
    {
        if t <= 0 {
            Self::all_unmarked(nums.len() as int)
        } else {
            let prev = Self::state_after(nums, queries, t - 1);
            Self::apply_query(nums, prev, queries[t - 1])
        }
    }

    pub open spec fn answers_prefix(nums: Seq<i32>, queries: Seq<Vec<i32>>, t: int) -> Seq<i64>
        decreases t,
    {
        if t <= 0 {
            seq![]
        } else {
            let prev = Self::answers_prefix(nums, queries, t - 1);
            let marks = Self::state_after(nums, queries, t);
            prev.push(Self::sum_unmarked(nums, marks) as i64)
        }
    }
}

pub open spec fn encode(v: int, i: int) -> int {
    v * 200000 + i
}

pub open spec fn decode_idx(e: int) -> int {
    e % 200000
}

proof fn lemma_encode_decode(v: int, i: int)
    requires 0 <= v <= 100000, 0 <= i < 200000,
    ensures decode_idx(encode(v, i)) == i,
{
    assert(encode(v, i) == v * 200000 + i);
}

proof fn lemma_encode_order(v1: int, i1: int, v2: int, i2: int)
    requires 0 <= v1 <= 100000, 0 <= i1 < 200000, 0 <= v2 <= 100000, 0 <= i2 < 200000,
    ensures
        encode(v1, i1) < encode(v2, i2) <==> (v1 < v2 || (v1 == v2 && i1 < i2)),
        encode(v1, i1) == encode(v2, i2) <==> (v1 == v2 && i1 == i2),
{
    if v1 < v2 {
        assert(encode(v1, i1) < encode(v2, i2)) by (nonlinear_arith)
            requires v1 < v2, 0 <= i1 < 200000, 0 <= i2 < 200000;
    } else if v1 > v2 {
        assert(encode(v1, i1) > encode(v2, i2)) by (nonlinear_arith)
            requires v1 > v2, 0 <= i1 < 200000, 0 <= i2 < 200000;
    }
}

pub open spec fn sorted_asc(s: Seq<int>) -> bool {
    forall|a: int, b: int| 0 <= a <= b < s.len() ==> s[a] <= s[b]
}

pub open spec fn merge_seq(a: Seq<int>, b: Seq<int>) -> Seq<int>
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        b
    } else if b.len() == 0 {
        a
    } else if a[0] <= b[0] {
        seq![a[0]] + merge_seq(a.drop_first(), b)
    } else {
        seq![b[0]] + merge_seq(a, b.drop_first())
    }
}

proof fn lemma_sorted_drop_first(s: Seq<int>)
    requires sorted_asc(s), s.len() >= 1,
    ensures sorted_asc(s.drop_first()),
{
    assert forall |a: int, b: int| 0 <= a <= b < s.drop_first().len() implies
        s.drop_first()[a] <= s.drop_first()[b] by {
        assert(s.drop_first()[a] == s[a + 1]);
        assert(s.drop_first()[b] == s[b + 1]);
    }
}

proof fn lemma_sorted_cons(x: int, rest: Seq<int>)
    requires sorted_asc(rest), rest.len() == 0 || x <= rest[0],
    ensures sorted_asc(seq![x] + rest),
{
    assert forall |a: int, b: int| 0 <= a <= b < (seq![x] + rest).len() implies
        (seq![x] + rest)[a] <= (seq![x] + rest)[b] by {
        if a == 0 {
            if b > 0 {
                assert((seq![x] + rest)[b] == rest[b - 1]);
                if b > 1 {
                    assert(rest[0] <= rest[b - 1]);
                }
            }
        } else {
            assert((seq![x] + rest)[a] == rest[a - 1]);
            assert((seq![x] + rest)[b] == rest[b - 1]);
        }
    }
}

proof fn lemma_merge_seq_all_ge(a: Seq<int>, b: Seq<int>, lo: int)
    requires
        forall |i: int| 0 <= i < a.len() ==> lo <= a[i],
        forall |i: int| 0 <= i < b.len() ==> lo <= b[i],
    ensures forall |i: int| 0 <= i < merge_seq(a, b).len() ==> lo <= #[trigger] merge_seq(a, b)[i],
    decreases a.len() + b.len(),
{
    if a.len() == 0 || b.len() == 0 {
    } else if a[0] <= b[0] {
        lemma_merge_seq_all_ge(a.drop_first(), b, lo);
        assert(merge_seq(a, b) =~= seq![a[0]] + merge_seq(a.drop_first(), b));
    } else {
        lemma_merge_seq_all_ge(a, b.drop_first(), lo);
        assert(merge_seq(a, b) =~= seq![b[0]] + merge_seq(a, b.drop_first()));
    }
}

proof fn lemma_merge_seq_sorted(a: Seq<int>, b: Seq<int>)
    requires sorted_asc(a), sorted_asc(b),
    ensures sorted_asc(merge_seq(a, b)),
    decreases a.len() + b.len(),
{
    if a.len() == 0 || b.len() == 0 {
    } else if a[0] <= b[0] {
        lemma_sorted_drop_first(a);
        lemma_merge_seq_sorted(a.drop_first(), b);
        if merge_seq(a.drop_first(), b).len() > 0 {
            if a.drop_first().len() > 0 {
                assert(a[0] <= a.drop_first()[0]);
            }
            lemma_merge_seq_all_ge(a.drop_first(), b, a[0]);
        }
        lemma_sorted_cons(a[0], merge_seq(a.drop_first(), b));
        assert(merge_seq(a, b) =~= seq![a[0]] + merge_seq(a.drop_first(), b));
    } else {
        lemma_sorted_drop_first(b);
        lemma_merge_seq_sorted(a, b.drop_first());
        if merge_seq(a, b.drop_first()).len() > 0 {
            if b.drop_first().len() > 0 {
                assert(b[0] <= b.drop_first()[0]);
            }
            lemma_merge_seq_all_ge(a, b.drop_first(), b[0]);
        }
        lemma_sorted_cons(b[0], merge_seq(a, b.drop_first()));
        assert(merge_seq(a, b) =~= seq![b[0]] + merge_seq(a, b.drop_first()));
    }
}

proof fn lemma_merge_seq_len(a: Seq<int>, b: Seq<int>)
    ensures merge_seq(a, b).len() == a.len() + b.len(),
    decreases a.len() + b.len(),
{
    if a.len() == 0 || b.len() == 0 {
    } else if a[0] <= b[0] {
        lemma_merge_seq_len(a.drop_first(), b);
    } else {
        lemma_merge_seq_len(a, b.drop_first());
    }
}

pub open spec fn merge_sort_seq(s: Seq<int>) -> Seq<int>
    decreases s.len()
{
    if s.len() <= 1 {
        s
    } else {
        let mid = s.len() as int / 2;
        merge_seq(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)))
    }
}

proof fn lemma_merge_sort_seq_sorted(s: Seq<int>)
    ensures sorted_asc(merge_sort_seq(s)),
    decreases s.len()
{
    if s.len() > 1 {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_sorted(s.subrange(0, mid));
        lemma_merge_sort_seq_sorted(s.subrange(mid, s.len() as int));
        lemma_merge_seq_sorted(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)));
    }
}

proof fn lemma_merge_sort_seq_len(s: Seq<int>)
    ensures merge_sort_seq(s).len() == s.len(),
    decreases s.len()
{
    if s.len() > 1 {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_len(s.subrange(0, mid));
        lemma_merge_sort_seq_len(s.subrange(mid, s.len() as int));
        lemma_merge_seq_len(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)));
    }
}

proof fn lemma_merge_seq_contains(a: Seq<int>, b: Seq<int>, v: int)
    ensures merge_seq(a, b).contains(v) <==> (a.contains(v) || b.contains(v)),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
        assert(merge_seq(a, b) =~= b);
    } else if b.len() == 0 {
        assert(merge_seq(a, b) =~= a);
    } else if a[0] <= b[0] {
        lemma_merge_seq_contains(a.drop_first(), b, v);
        assert(merge_seq(a, b) =~= seq![a[0]] + merge_seq(a.drop_first(), b));
        assert(a =~= seq![a[0]] + a.drop_first());
        lemma_seq_concat_contains_all_elements(seq![a[0]], merge_seq(a.drop_first(), b), v);
        lemma_seq_concat_contains_all_elements(seq![a[0]], a.drop_first(), v);
        assert(seq![a[0]][0] == a[0]);
        if seq![a[0]].contains(v) {
            let k = choose |k: int| 0 <= k < seq![a[0]].len() && seq![a[0]][k] == v;
            assert(k == 0);
        }
    } else {
        lemma_merge_seq_contains(a, b.drop_first(), v);
        assert(merge_seq(a, b) =~= seq![b[0]] + merge_seq(a, b.drop_first()));
        lemma_seq_concat_contains_all_elements(seq![b[0]], merge_seq(a, b.drop_first()), v);
        lemma_seq_concat_contains_all_elements(seq![b[0]], b.drop_first(), v);
        assert(seq![b[0]][0] == b[0]);
        if seq![b[0]].contains(v) {
            let k = choose |k: int| 0 <= k < seq![b[0]].len() && seq![b[0]][k] == v;
            assert(k == 0);
        }
        assert(b =~= seq![b[0]] + b.drop_first());
    }
}

proof fn lemma_merge_sort_seq_contains(s: Seq<int>, v: int)
    ensures merge_sort_seq(s).contains(v) <==> s.contains(v),
    decreases s.len(),
{
    if s.len() <= 1 {
    } else {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_contains(s.subrange(0, mid), v);
        lemma_merge_sort_seq_contains(s.subrange(mid, s.len() as int), v);
        lemma_merge_seq_contains(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)), v);
        assert(s =~= s.subrange(0, mid) + s.subrange(mid, s.len() as int));
        assert forall |x: int| s.contains(x) implies (s.subrange(0, mid).contains(x) || s.subrange(mid, s.len() as int).contains(x)) by {
            if s.contains(x) {
                let k = choose |k: int| 0 <= k < s.len() && s[k] == x;
                if k < mid {
                    assert(s.subrange(0, mid)[k] == x);
                } else {
                    assert(s.subrange(mid, s.len() as int)[k - mid] == x);
                }
            }
        }
        assert forall |x: int| (s.subrange(0, mid).contains(x) || s.subrange(mid, s.len() as int).contains(x)) implies s.contains(x) by {
            if s.subrange(0, mid).contains(x) {
                let k = choose |k: int| 0 <= k < mid && s.subrange(0, mid)[k] == x;
                assert(s[k] == x);
            }
            if s.subrange(mid, s.len() as int).contains(x) {
                let k = choose |k: int| 0 <= k < s.len() - mid && s.subrange(mid, s.len() as int)[k] == x;
                assert(s[k + mid] == x);
            }
        }
    }
}

proof fn lemma_best_in_prefix_char(nums: Seq<i32>, marked: Seq<bool>, end: int)
    requires
        0 <= end <= nums.len(),
        nums.len() <= 100000,
        marked.len() == nums.len(),
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000,
    ensures
        ({
            let b = Solution::best_in_prefix(nums, marked, end);
            &&& (b == nums.len() as int ==> forall |i: int| 0 <= i < end ==> #[trigger] marked[i])
            &&& (b != nums.len() as int ==> {
                &&& 0 <= b < end
                &&& !marked[b]
                &&& forall |i: int| 0 <= i < end && !marked[i] ==>
                    encode(nums[b] as int, b) <= #[trigger] encode(nums[i] as int, i)
            })
        }),
    decreases end,
{
    if end > 0 {
        lemma_best_in_prefix_char(nums, marked, end - 1);
        let prev = Solution::best_in_prefix(nums, marked, end - 1);
        let j = end - 1;
        if !marked[j] && prev != nums.len() as int {
            lemma_encode_order(nums[j] as int, j, nums[prev] as int, prev);
        }
    }
}

pub open spec fn pts_encoded(nums: Seq<i32>) -> Seq<int>
    decreases nums.len()
{
    if nums.len() == 0 {
        Seq::empty()
    } else {
        pts_encoded(nums.subrange(0, nums.len() - 1)).push(encode(nums[nums.len() - 1] as int, nums.len() - 1))
    }
}

proof fn lemma_pts_encoded_len(nums: Seq<i32>)
    ensures pts_encoded(nums).len() == nums.len(),
    decreases nums.len(),
{
    if nums.len() > 0 {
        lemma_pts_encoded_len(nums.subrange(0, nums.len() - 1));
    }
}

proof fn lemma_pts_encoded_index(nums: Seq<i32>, i: int)
    requires 0 <= i < nums.len(),
    ensures pts_encoded(nums)[i] == encode(nums[i] as int, i),
    decreases nums.len(),
{
    lemma_pts_encoded_len(nums);
    if i < nums.len() - 1 {
        lemma_pts_encoded_index(nums.subrange(0, nums.len() - 1), i);
        assert(nums.subrange(0, nums.len() - 1)[i] == nums[i]);
    }
}

pub open spec fn sorted_enc(nums: Seq<i32>) -> Seq<int> {
    merge_sort_seq(pts_encoded(nums))
}

proof fn lemma_sorted_enc_props(nums: Seq<i32>)
    ensures
        sorted_asc(sorted_enc(nums)),
        sorted_enc(nums).len() == nums.len(),
        forall |v: int| sorted_enc(nums).contains(v) <==> pts_encoded(nums).contains(v),
{
    lemma_merge_sort_seq_sorted(pts_encoded(nums));
    lemma_merge_sort_seq_len(pts_encoded(nums));
    lemma_pts_encoded_len(nums);
    assert forall |v: int| sorted_enc(nums).contains(v) <==> pts_encoded(nums).contains(v) by {
        lemma_merge_sort_seq_contains(pts_encoded(nums), v);
    }
}

proof fn lemma_sorted_enc_pos_to_index(nums: Seq<i32>, p: int)
    requires
        0 <= p < nums.len(),
        nums.len() <= 100000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000,
    ensures
        0 <= decode_idx(sorted_enc(nums)[p]) < nums.len(),
        sorted_enc(nums)[p] == encode(nums[decode_idx(sorted_enc(nums)[p])] as int, decode_idx(sorted_enc(nums)[p])),
{
    lemma_sorted_enc_props(nums);
    assert(sorted_enc(nums).contains(sorted_enc(nums)[p]));
    assert(pts_encoded(nums).contains(sorted_enc(nums)[p]));
    lemma_pts_encoded_len(nums);
    let i = choose |i: int| 0 <= i < nums.len() && pts_encoded(nums)[i] == sorted_enc(nums)[p];
    lemma_pts_encoded_index(nums, i);
    assert(sorted_enc(nums)[p] == encode(nums[i] as int, i));
    lemma_encode_decode(nums[i] as int, i);
    assert(decode_idx(sorted_enc(nums)[p]) == i);
}

proof fn lemma_sorted_enc_surjective(nums: Seq<i32>, i: int)
    requires
        0 <= i < nums.len(),
        nums.len() <= 100000,
        forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100000,
    ensures exists |p: int| 0 <= p < nums.len() && decode_idx(sorted_enc(nums)[p]) == i,
{
    lemma_sorted_enc_props(nums);
    lemma_pts_encoded_len(nums);
    lemma_pts_encoded_index(nums, i);
    assert(pts_encoded(nums).contains(pts_encoded(nums)[i]));
    assert(sorted_enc(nums).contains(pts_encoded(nums)[i]));
    let p = choose |p: int| 0 <= p < sorted_enc(nums).len() && sorted_enc(nums)[p] == pts_encoded(nums)[i];
    lemma_sorted_enc_pos_to_index(nums, p);
    let j = decode_idx(sorted_enc(nums)[p]);
    assert(sorted_enc(nums)[p] == encode(nums[j] as int, j));
    assert(sorted_enc(nums)[p] == encode(nums[i] as int, i));
    lemma_encode_order(nums[j] as int, j, nums[i] as int, i);
    assert(j == i);
}

proof fn lemma_best_unmarked_pointer_char(nums: Seq<i32>, marked: Seq<bool>, ptr: int)
    requires
        nums.len() <= 100000,
        marked.len() == nums.len(),
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000,
        0 <= ptr <= nums.len(),
        forall |p: int| 0 <= p < ptr ==> #[trigger] marked[decode_idx(sorted_enc(nums)[p])],
        ptr == nums.len() || !marked[decode_idx(sorted_enc(nums)[ptr])],
    ensures
        Solution::best_unmarked(nums, marked)
            == if ptr == nums.len() { nums.len() as int } else { decode_idx(sorted_enc(nums)[ptr]) },
{
    lemma_best_in_prefix_char(nums, marked, nums.len() as int);
    lemma_sorted_enc_props(nums);
    let b = Solution::best_unmarked(nums, marked);
    if ptr == nums.len() as int {
        assert forall |p: int| 0 <= p < nums.len() implies #[trigger] marked[decode_idx(sorted_enc(nums)[p])] by {}
        assert forall |i: int| 0 <= i < nums.len() implies #[trigger] marked[i] by {
            lemma_pts_encoded_len(nums);
            lemma_pts_encoded_index(nums, i);
            assert(pts_encoded(nums)[i] == encode(nums[i] as int, i));
            assert(pts_encoded(nums).contains(pts_encoded(nums)[i]));
            assert(pts_encoded(nums).contains(encode(nums[i] as int, i)));
            assert(sorted_enc(nums).contains(encode(nums[i] as int, i)));
            let p = choose |p: int| 0 <= p < nums.len() && sorted_enc(nums)[p] == encode(nums[i] as int, i);
            lemma_sorted_enc_pos_to_index(nums, p);
            assert(decode_idx(sorted_enc(nums)[p]) == i);
        }
        assert(b == nums.len() as int);
    } else {
        lemma_sorted_enc_pos_to_index(nums, ptr);
        let target = decode_idx(sorted_enc(nums)[ptr]);
        assert(!marked[target]);
        assert(b != nums.len() as int) by {
            if b == nums.len() as int {
                assert(marked[target]);
            }
        }
        assert(0 <= b < nums.len());
        assert(!marked[b]);
        assert(encode(nums[b] as int, b) <= encode(nums[target] as int, target));

        lemma_sorted_enc_pos_to_index(nums, b);
        assert(sorted_enc(nums).contains(encode(nums[b] as int, b))) by {
            lemma_pts_encoded_len(nums);
            lemma_pts_encoded_index(nums, b);
            assert(pts_encoded(nums)[b] == encode(nums[b] as int, b));
            assert(pts_encoded(nums).contains(pts_encoded(nums)[b]));
            assert(pts_encoded(nums).contains(encode(nums[b] as int, b)));
        }
        let q = choose |q: int| 0 <= q < nums.len() && sorted_enc(nums)[q] == encode(nums[b] as int, b);
        if q < ptr {
            assert(marked[decode_idx(sorted_enc(nums)[q])]);
            lemma_sorted_enc_pos_to_index(nums, q);
            assert(decode_idx(sorted_enc(nums)[q]) == b);
            assert(false);
        }
        assert(q >= ptr);
        assert(sorted_enc(nums)[ptr] <= sorted_enc(nums)[q]);
        assert(encode(nums[target] as int, target) <= encode(nums[b] as int, b));
        assert(encode(nums[b] as int, b) == encode(nums[target] as int, target));
        lemma_encode_order(nums[b] as int, b, nums[target] as int, target);
        assert(b == target);
    }
}

proof fn lemma_sum_unmarked_prefix_nonneg(nums: Seq<i32>, marked: Seq<bool>, end: int)
    requires
        marked.len() == nums.len(),
        0 <= end <= nums.len(),
        forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] >= 0,
    ensures Solution::sum_unmarked_prefix(nums, marked, end) >= 0,
    decreases end,
{
    if end > 0 {
        lemma_sum_unmarked_prefix_nonneg(nums, marked, end - 1);
    }
}

proof fn lemma_sum_unmarked_nonneg(nums: Seq<i32>, marked: Seq<bool>)
    requires
        marked.len() == nums.len(),
        forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] >= 0,
    ensures Solution::sum_unmarked(nums, marked) >= 0,
{
    lemma_sum_unmarked_prefix_nonneg(nums, marked, nums.len() as int);
}

proof fn lemma_sum_unmarked_mark_one(nums: Seq<i32>, marked: Seq<bool>, target: int)
    requires
        marked.len() == nums.len(),
        0 <= target < nums.len(),
        !marked[target],
    ensures
        Solution::sum_unmarked(nums, marked.update(target, true))
            == Solution::sum_unmarked(nums, marked) - nums[target] as int,
{
    lemma_sum_unmarked_prefix_mark_one(nums, marked, target, nums.len() as int);
}

proof fn lemma_sum_unmarked_prefix_mark_one(nums: Seq<i32>, marked: Seq<bool>, target: int, end: int)
    requires
        marked.len() == nums.len(),
        0 <= target < nums.len(),
        !marked[target],
        0 <= end <= nums.len(),
    ensures
        end <= target ==> Solution::sum_unmarked_prefix(nums, marked.update(target, true), end)
            == Solution::sum_unmarked_prefix(nums, marked, end),
        end > target ==> Solution::sum_unmarked_prefix(nums, marked.update(target, true), end)
            == Solution::sum_unmarked_prefix(nums, marked, end) - nums[target] as int,
    decreases end,
{
    if end > 0 {
        lemma_sum_unmarked_prefix_mark_one(nums, marked, target, end - 1);
        assert(marked.update(target, true)[end - 1] == (if end - 1 == target { true } else { marked[end - 1] }));
    }
}

pub open spec fn to_int_seq64(s: Seq<i64>) -> Seq<int> {
    s.map_values(|x: i64| x as int)
}

proof fn lemma_merge_seq_skip_step_a(a: Seq<int>, b: Seq<int>, i: int, j: int)
    requires 0 <= i < a.len(), 0 <= j <= b.len(), (j >= b.len() || a[i] <= b[j]),
    ensures merge_seq(a.skip(i), b.skip(j)) =~= seq![a[i]] + merge_seq(a.skip(i + 1), b.skip(j)),
{
    assert(a.skip(i)[0] == a[i]);
    assert(a.skip(i).drop_first() =~= a.skip(i + 1));
    if j < b.len() {
        assert(b.skip(j)[0] == b[j]);
        assert(a.skip(i)[0] <= b.skip(j)[0]);
    } else {
        assert(b.skip(j).len() == 0);
    }
}

proof fn lemma_merge_seq_skip_step_b(a: Seq<int>, b: Seq<int>, i: int, j: int)
    requires 0 <= i <= a.len(), 0 <= j < b.len(), (i >= a.len() || b[j] < a[i]),
    ensures merge_seq(a.skip(i), b.skip(j)) =~= seq![b[j]] + merge_seq(a.skip(i), b.skip(j + 1)),
{
    assert(b.skip(j)[0] == b[j]);
    assert(b.skip(j).drop_first() =~= b.skip(j + 1));
    if i < a.len() {
        assert(a.skip(i)[0] == a[i]);
        assert(b.skip(j)[0] < a.skip(i)[0]);
    } else {
        assert(a.skip(i).len() == 0);
    }
}

fn merge_exec(a: &Vec<i64>, b: &Vec<i64>) -> (result: Vec<i64>)
    requires
        sorted_asc(to_int_seq64(a@)),
        sorted_asc(to_int_seq64(b@)),
    ensures
        to_int_seq64(result@) == merge_seq(to_int_seq64(a@), to_int_seq64(b@)),
{
    let ghost av = to_int_seq64(a@);
    let ghost bv = to_int_seq64(b@);
    let mut result: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    proof {
        assert(av.skip(0) =~= av);
        assert(bv.skip(0) =~= bv);
        assert(to_int_seq64(result@) =~= Seq::<int>::empty());
    }
    while i < a.len() || j < b.len()
        invariant
            i <= a.len(),
            j <= b.len(),
            result.len() == i + j,
            to_int_seq64(a@) == av,
            to_int_seq64(b@) == bv,
            to_int_seq64(result@) + merge_seq(av.skip(i as int), bv.skip(j as int)) == merge_seq(av, bv),
        decreases (a.len() - i) + (b.len() - j),
    {
        if j >= b.len() || (i < a.len() && a[i] <= b[j]) {
            proof {
                lemma_merge_seq_skip_step_a(av, bv, i as int, j as int);
                assert(to_int_seq64(result@).push(a@[i as int] as int) =~= to_int_seq64(result@) + seq![a@[i as int] as int]);
            }
            result.push(a[i]);
            i += 1;
        } else {
            proof {
                lemma_merge_seq_skip_step_b(av, bv, i as int, j as int);
                assert(to_int_seq64(result@).push(b@[j as int] as int) =~= to_int_seq64(result@) + seq![b@[j as int] as int]);
            }
            result.push(b[j]);
            j += 1;
        }
    }
    proof {
        assert(av.skip(i as int).len() == 0);
        assert(bv.skip(j as int).len() == 0);
        assert(merge_seq(av.skip(i as int), bv.skip(j as int)) =~= Seq::<int>::empty());
        assert(to_int_seq64(result@) == merge_seq(av, bv));
    }
    result
}

fn merge_sort_exec(v: &Vec<i64>) -> (result: Vec<i64>)
    requires v.len() <= 100_000,
    ensures to_int_seq64(result@) == merge_sort_seq(to_int_seq64(v@)),
    decreases v.len()
{
    if v.len() <= 1 {
        let mut result: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < v.len()
            invariant k <= v.len(), result@.len() == k as int,
                forall |t: int| 0 <= t < k ==> result@[t] == v@[t],
            decreases v.len() - k,
        {
            result.push(v[k]);
            k += 1;
        }
        proof {
            assert(result@ =~= v@);
        }
        result
    } else {
        let mid = v.len() / 2;
        let mut left: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < mid
            invariant i <= mid, mid <= v.len(), left@.len() == i as int,
                forall |t: int| 0 <= t < i ==> left@[t] == v@[t],
            decreases mid - i,
        {
            left.push(v[i]);
            i += 1;
        }
        let mut right: Vec<i64> = Vec::new();
        let mut i2: usize = mid;
        while i2 < v.len()
            invariant mid <= i2 <= v.len(), right@.len() == i2 - mid,
                forall |t: int| 0 <= t < i2 - mid ==> right@[t as int] == v@[t + mid as int],
            decreases v.len() - i2,
        {
            right.push(v[i2]);
            i2 += 1;
        }
        proof {
            assert(left@ =~= v@.subrange(0, mid as int));
            assert(right@ =~= v@.subrange(mid as int, v@.len() as int));
        }
        let sorted_left = merge_sort_exec(&left);
        let sorted_right = merge_sort_exec(&right);
        proof {
            lemma_merge_sort_seq_sorted(to_int_seq64(v@).subrange(0, mid as int));
            lemma_merge_sort_seq_sorted(to_int_seq64(v@).subrange(mid as int, v@.len() as int));
            assert(to_int_seq64(left@) =~= to_int_seq64(v@).subrange(0, mid as int));
            assert(to_int_seq64(right@) =~= to_int_seq64(v@).subrange(mid as int, v@.len() as int));
        }
        let result = merge_exec(&sorted_left, &sorted_right);
        proof {
            assert(to_int_seq64(result@) == merge_seq(to_int_seq64(sorted_left@), to_int_seq64(sorted_right@)));
            assert(merge_sort_seq(to_int_seq64(v@)) ==
                merge_seq(merge_sort_seq(to_int_seq64(v@).subrange(0, mid as int)),
                    merge_sort_seq(to_int_seq64(v@).subrange(mid as int, v@.len() as int))));
        }
        result
    }
}

fn encode_exec(v: i32, i: usize) -> (result: i64)
    requires 1 <= v <= 100000, i < 100000,
    ensures result as int == encode(v as int, i as int),
{
    (v as i64) * 200000 + (i as i64)
}

fn decode_idx_exec(e: i64) -> (result: i64)
    requires 0 <= e <= 100000i64 * 200000i64 + 199999i64,
    ensures result as int == decode_idx(e as int),
{
    e % 200000
}

proof fn lemma_all_unmarked_len(n: int)
    requires n >= 0,
    ensures Solution::all_unmarked(n).len() == n,
    decreases n,
{
    if n > 0 {
        lemma_all_unmarked_len(n - 1);
    }
}

proof fn lemma_all_unmarked_false(n: int, i: int)
    requires 0 <= i < n,
    ensures !Solution::all_unmarked(n)[i],
    decreases n,
{
    lemma_all_unmarked_len(n);
    if i < n - 1 {
        lemma_all_unmarked_false(n - 1, i);
    }
}

proof fn lemma_best_in_prefix_all_marked(nums: Seq<i32>, marked: Seq<bool>, end: int)
    requires
        0 <= end <= nums.len(),
        marked.len() == nums.len(),
        forall |i: int| 0 <= i < end ==> #[trigger] marked[i],
    ensures Solution::best_in_prefix(nums, marked, end) == nums.len() as int,
    decreases end,
{
    if end > 0 {
        lemma_best_in_prefix_all_marked(nums, marked, end - 1);
    }
}

proof fn lemma_mark_steps_compose(nums: Seq<i32>, marked: Seq<bool>, a: int, b: int)
    requires marked.len() == nums.len(), a >= 0, b >= 0,
    ensures Solution::mark_steps(nums, marked, a + b)
        == Solution::mark_steps(nums, Solution::mark_steps(nums, marked, a), b),
    decreases b,
{
    if b > 0 {
        lemma_mark_steps_compose(nums, marked, a, b - 1);
    }
}

proof fn lemma_mark_steps_stable_when_full(nums: Seq<i32>, marked: Seq<bool>, extra: int)
    requires
        marked.len() == nums.len(),
        forall |i: int| 0 <= i < nums.len() ==> #[trigger] marked[i],
        extra >= 0,
    ensures Solution::mark_steps(nums, marked, extra) == marked,
    decreases extra,
{
    if extra > 0 {
        lemma_mark_steps_stable_when_full(nums, marked, extra - 1);
        lemma_best_in_prefix_all_marked(nums, marked, nums.len() as int);
    }
}

proof fn lemma_sum_unmarked_prefix_all_false(nums: Seq<i32>, end: int)
    requires 0 <= end <= nums.len(),
    ensures Solution::sum_unmarked_prefix(nums, Solution::all_unmarked(nums.len() as int), end)
        == Solution::sum_unmarked_prefix(nums, Solution::all_unmarked(nums.len() as int), end - 1)
            + (if end > 0 { nums[end - 1] as int } else { 0 }),
{
    if end > 0 {
        lemma_all_unmarked_false(nums.len() as int, end - 1);
    }
}

proof fn lemma_sorted_enc_bulk(nums: Seq<i32>)
    requires
        nums.len() <= 100000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000,
    ensures
        sorted_enc(nums).len() == nums.len(),
        forall |p: int| 0 <= p < nums.len() ==>
            0 <= #[trigger] decode_idx(sorted_enc(nums)[p]) < nums.len(),
        forall |p: int| 0 <= p < nums.len() ==>
            0 <= #[trigger] sorted_enc(nums)[p] <= 100000 * 200000 + 99999,
{
    lemma_sorted_enc_props(nums);
    assert forall |p: int| 0 <= p < nums.len() implies
        0 <= #[trigger] decode_idx(sorted_enc(nums)[p]) < nums.len() by {
        lemma_sorted_enc_pos_to_index(nums, p);
    }
    assert forall |p: int| 0 <= p < nums.len() implies
        0 <= #[trigger] sorted_enc(nums)[p] <= 100000 * 200000 + 99999 by {
        lemma_sorted_enc_pos_to_index(nums, p);
        let idx = decode_idx(sorted_enc(nums)[p]);
        assert(sorted_enc(nums)[p] == encode(nums[idx] as int, idx));
        assert(0 <= idx < nums.len());
        assert(1 <= nums[idx] <= 100000);
        assert(encode(nums[idx] as int, idx) == nums[idx] as int * 200000 + idx);
        assert(nums[idx] as int * 200000 + idx <= 100000 * 200000 + 99999) by (nonlinear_arith)
            requires nums[idx] as int <= 100000, 0 <= idx <= 99999;
    }
}

impl Solution {
    pub fn unmarked_sum_array(nums: Vec<i32>, queries: Vec<Vec<i32>>) -> (result: Vec<i64>)
        requires
            1 <= queries.len() <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
            forall |i: int| 0 <= i < queries.len() ==> #[trigger] queries[i].len() == 2,
            forall |i: int| 0 <= i < queries.len() && queries[i].len() == 2 ==> 0 <= #[trigger] queries[i][0] < nums.len(),
            forall |i: int| 0 <= i < queries.len() && queries[i].len() == 2 ==> 0 <= #[trigger] queries[i][1] <= nums.len() - 1,
        ensures
            result@ == Self::answers_prefix(nums@, queries@, queries.len() as int),
    {
        let n = nums.len();
        let ghost se = sorted_enc(nums@);
        proof {
            lemma_sorted_enc_props(nums@);
        }

        let mut enc: Vec<i64> = Vec::new();
        let mut ii: usize = 0;
        while ii < n
            invariant
                ii <= n,
                n == nums.len(),
                n <= 100000,
                forall |i: int| 0 <= i < n as int ==> 1 <= #[trigger] nums@[i] <= 100000,
                enc@.len() == ii,
                forall |k: int| 0 <= k < ii ==> enc@[k] as int == encode(nums@[k] as int, k),
            decreases n - ii,
        {
            proof {
                assert(ii < 100000);
                assert(1 <= nums@[ii as int] <= 100000);
            }
            let e = encode_exec(nums[ii], ii);
            enc.push(e);
            ii += 1;
        }
        proof {
            assert forall |k: int| 0 <= k < n as int implies to_int_seq64(enc@)[k] == pts_encoded(nums@)[k] by {
                lemma_pts_encoded_index(nums@, k);
            }
            assert(to_int_seq64(enc@).len() == pts_encoded(nums@).len()) by {
                lemma_pts_encoded_len(nums@);
            }
            assert(to_int_seq64(enc@) =~= pts_encoded(nums@));
        }
        let sorted = merge_sort_exec(&enc);
        proof {
            assert(to_int_seq64(sorted@) =~= se);
            assert(to_int_seq64(sorted@) == se);
        }

        let mut marked: Vec<bool> = Vec::new();
        let mut jj: usize = 0;
        while jj < n
            invariant jj <= n, marked@.len() == jj,
                forall |k: int| 0 <= k < jj ==> !marked@[k],
            decreases n - jj,
        {
            marked.push(false);
            jj += 1;
        }
        proof {
            assert(marked@ =~= Solution::all_unmarked(n as int)) by {
                lemma_all_unmarked_len(n as int);
                assert forall |k: int| 0 <= k < n as int implies marked@[k] == Solution::all_unmarked(n as int)[k] by {
                    lemma_all_unmarked_false(n as int, k);
                }
            }
        }

        let mut total: i64 = 0;
        let mut pp: usize = 0;
        while pp < n
            invariant
                pp <= n,
                n == nums.len(),
                n <= 100000,
                forall |i: int| 0 <= i < n as int ==> 1 <= #[trigger] nums@[i] <= 100000,
                total as int == Solution::sum_unmarked_prefix(nums@, Solution::all_unmarked(n as int), pp as int),
                0 <= total <= 100000 * pp as i64,
            decreases n - pp,
        {
            proof {
                lemma_sum_unmarked_prefix_all_false(nums@, pp as int + 1);
                assert(nums@[pp as int] <= 100000);
                assert(total + nums@[pp as int] as i64 <= 100000 * (pp as i64 + 1)) by (nonlinear_arith)
                    requires total <= 100000 * pp as i64, nums@[pp as int] <= 100000;
            }
            total = total + nums[pp] as i64;
            pp += 1;
        }
        let mut unmarked_sum: i64 = total;
        proof {
            assert(unmarked_sum as int == Solution::sum_unmarked(nums@, marked@));
        }

        proof {
            lemma_sorted_enc_bulk(nums@);
        }

        let mut ptr: usize = 0;
        let mut result: Vec<i64> = Vec::new();
        let mut q: usize = 0;
        while q < queries.len()
            invariant
                q <= queries.len(),
                n == nums.len(),
                n <= 100000,
                queries.len() <= n,
                forall |i: int| 0 <= i < n as int ==> 1 <= #[trigger] nums@[i] <= 100000,
                forall |i: int| 0 <= i < queries.len() ==> #[trigger] queries@[i].len() == 2,
                forall |i: int| 0 <= i < queries.len() ==> 0 <= #[trigger] queries@[i][0] < n as int,
                forall |i: int| 0 <= i < queries.len() ==> 0 <= #[trigger] queries@[i][1] <= n as int - 1,
                marked@.len() == n,
                ptr <= n,
                to_int_seq64(sorted@) == se,
                sorted@.len() == n,
                se == sorted_enc(nums@),
                se.len() == n,
                forall |p: int| 0 <= p < n as int ==> 0 <= #[trigger] decode_idx(se[p]) < n as int,
                forall |p: int| 0 <= p < n as int ==> 0 <= #[trigger] se[p] <= 100000 * 200000 + 99999,
                forall |p: int| 0 <= p < ptr as int ==> #[trigger] marked@[decode_idx(se[p])],
                marked@ == Solution::state_after(nums@, queries@, q as int),
                unmarked_sum as int == Solution::sum_unmarked(nums@, marked@),
                0 <= unmarked_sum,
                result@.len() == q,
                result@ == Solution::answers_prefix(nums@, queries@, q as int),
            decreases queries.len() - q,
        {
            proof {
                assert(queries@[q as int].len() == 2);
            }
            let idx = queries[q][0] as usize;
            let k = queries[q][1];
            let ghost marked_before_query = marked@;
            if !marked[idx] {
                proof {
                    lemma_sum_unmarked_mark_one(nums@, marked@, idx as int);
                    lemma_sum_unmarked_nonneg(nums@, marked@.update(idx as int, true));
                    assert(0 <= unmarked_sum - nums@[idx as int] as i64);
                }
                marked.set(idx, true);
                unmarked_sum = unmarked_sum - nums[idx] as i64;
            }
            let ghost marked1 = marked@;
            proof {
                assert(marked1 =~= Solution::mark_index(marked_before_query, idx as int));
                assert(marked@ == Solution::mark_steps(nums@, marked1, 0));
            }

            let mut t: i32 = 0;
            while t < k && ptr < n
                invariant
                    0 <= t <= k,
                    n == nums.len(),
                    n <= 100000,
                    forall |i: int| 0 <= i < n as int ==> 1 <= #[trigger] nums@[i] <= 100000,
                    marked@.len() == n,
                    ptr <= n,
                    to_int_seq64(sorted@) == se,
                    sorted@.len() == n,
                    se == sorted_enc(nums@),
                    se.len() == n,
                    forall |p: int| 0 <= p < n as int ==> 0 <= #[trigger] decode_idx(se[p]) < n as int,
                    forall |p: int| 0 <= p < n as int ==> 0 <= #[trigger] se[p] <= 100000 * 200000 + 99999,
                    forall |p: int| 0 <= p < ptr as int ==> #[trigger] marked@[decode_idx(se[p])],
                    marked@ == Solution::mark_steps(nums@, marked1, t as int),
                    unmarked_sum as int == Solution::sum_unmarked(nums@, marked@),
                    0 <= unmarked_sum,
                decreases k - t,
            {
                let ghost marked_before_step = marked@;
                let mut cont: bool = false;
                if ptr < n {
                    let sp = sorted[ptr];
                    proof {
                        assert(sp as int == to_int_seq64(sorted@)[ptr as int]);
                        assert(to_int_seq64(sorted@)[ptr as int] == se[ptr as int]);
                        assert(0 <= sp <= 100000i64 * 200000i64 + 99999i64);
                    }
                    let di = decode_idx_exec(sp);
                    proof {
                        assert(di as int == decode_idx(se[ptr as int]));
                        assert(0 <= di < n as i64);
                    }
                    cont = marked[di as usize];
                }
                while cont
                    invariant
                        ptr <= n,
                        n == nums.len(),
                        n <= 100000,
                        marked@.len() == n,
                        to_int_seq64(sorted@) == se,
                        sorted@.len() == n,
                        se == sorted_enc(nums@),
                        se.len() == n,
                        forall |p: int| 0 <= p < n as int ==> 0 <= #[trigger] decode_idx(se[p]) < n as int,
                        forall |p: int| 0 <= p < n as int ==> 0 <= #[trigger] se[p] <= 100000 * 200000 + 99999,
                        marked@ == marked_before_step,
                        forall |p: int| 0 <= p < ptr as int ==> #[trigger] marked@[decode_idx(se[p])],
                        cont ==> ptr < n,
                        ptr < n ==> cont == marked@[decode_idx(se[ptr as int])],
                    decreases n - ptr,
                {
                    ptr += 1;
                    cont = false;
                    if ptr < n {
                        let sp = sorted[ptr];
                        proof {
                            assert(sp as int == to_int_seq64(sorted@)[ptr as int]);
                            assert(to_int_seq64(sorted@)[ptr as int] == se[ptr as int]);
                            assert(0 <= sp <= 100000i64 * 200000i64 + 99999i64);
                        }
                        let di = decode_idx_exec(sp);
                        proof {
                            assert(di as int == decode_idx(se[ptr as int]));
                            assert(0 <= di < n as i64);
                        }
                        cont = marked[di as usize];
                    }
                }
                proof {
                    assert(ptr == n || !marked@[decode_idx(se[ptr as int])]);
                    lemma_best_unmarked_pointer_char(nums@, marked@, ptr as int);
                }
                if ptr < n {
                    let sp2 = sorted[ptr];
                    proof {
                        assert(sp2 as int == to_int_seq64(sorted@)[ptr as int]);
                        assert(to_int_seq64(sorted@)[ptr as int] == se[ptr as int]);
                        assert(0 <= sp2 <= 100000i64 * 200000i64 + 99999i64);
                    }
                    let di2 = decode_idx_exec(sp2);
                    proof {
                        assert(di2 as int == decode_idx(se[ptr as int]));
                        assert(0 <= di2 < n as i64);
                    }
                    let target = di2 as usize;
                    proof {
                        assert(Solution::best_unmarked(nums@, marked@) == target as int);
                        assert(!marked@[target as int]);
                        lemma_sum_unmarked_mark_one(nums@, marked@, target as int);
                        lemma_sum_unmarked_nonneg(nums@, marked@.update(target as int, true));
                        assert(0 <= unmarked_sum - nums@[target as int] as i64);
                    }
                    marked.set(target, true);
                    unmarked_sum = unmarked_sum - nums[target] as i64;
                    ptr += 1;
                    proof {
                        assert(Solution::mark_steps(nums@, marked1, t as int + 1)
                            == marked_before_step.update(target as int, true));
                    }
                } else {
                    proof {
                        assert(Solution::best_unmarked(nums@, marked@) == n as int);
                        assert(Solution::mark_steps(nums@, marked1, t as int + 1) == marked_before_step);
                    }
                }
                t += 1;
            }
            proof {
                if t < k {
                    assert(ptr == n);
                    assert forall |i: int| 0 <= i < n as int implies #[trigger] marked@[i] by {
                        lemma_sorted_enc_surjective(nums@, i);
                        let p = choose |p: int| 0 <= p < n as int && decode_idx(se[p]) == i;
                        assert(marked@[decode_idx(se[p])]);
                    }
                    lemma_mark_steps_stable_when_full(nums@, marked@, k as int - t as int);
                    assert(Solution::mark_steps(nums@, marked@, k as int - t as int) == marked@);
                    lemma_mark_steps_compose(nums@, marked1, t as int, k as int - t as int);
                    assert(Solution::mark_steps(nums@, marked1, t as int + (k as int - t as int))
                        == Solution::mark_steps(nums@, Solution::mark_steps(nums@, marked1, t as int), k as int - t as int));
                    assert(Solution::mark_steps(nums@, marked1, t as int) == marked@);
                    assert(t as int + (k as int - t as int) == k as int);
                    assert(Solution::mark_steps(nums@, marked1, k as int) == marked@);
                }
                assert(marked@ == Solution::apply_query(nums@, marked_before_query, queries@[q as int]));
                assert(Solution::state_after(nums@, queries@, q as int + 1)
                    == Solution::apply_query(nums@, Solution::state_after(nums@, queries@, q as int), queries@[q as int]));
            }
            result.push(unmarked_sum);
            proof {
                assert(Solution::answers_prefix(nums@, queries@, q as int + 1)
                    =~= Solution::answers_prefix(nums@, queries@, q as int).push(unmarked_sum as int as i64));
            }
            q += 1;
        }
        result
    }
}

}
