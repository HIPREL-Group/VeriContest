use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn subarray_sum(nums: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end { 0 }
    else { nums[start] as int + subarray_sum(nums, start + 1, end) }
}

pub open spec fn sums_from(nums: Seq<i32>, start: int, end: int) -> Seq<i32>
    decreases nums.len() as int + 1 - end,
{
    if end > nums.len() || end <= start { Seq::<i32>::empty() }
    else {
        seq![subarray_sum(nums, start, end) as i32] + sums_from(nums, start, end + 1)
    }
}

pub open spec fn all_sums_seq(nums: Seq<i32>, i: int) -> Seq<i32>
    decreases nums.len() - i,
{
    if i >= nums.len() { Seq::<i32>::empty() }
    else {
        sums_from(nums, i, i + 1) + all_sums_seq(nums, i + 1)
    }
}

pub open spec fn spec_insert(sorted: Seq<i32>, val: i32) -> Seq<i32>
    decreases sorted.len(),
{
    if sorted.len() == 0 { seq![val] }
    else if val <= sorted[0] { seq![val] + sorted }
    else { seq![sorted[0]] + spec_insert(sorted.subrange(1, sorted.len() as int), val) }
}

pub open spec fn spec_sort(s: Seq<i32>) -> Seq<i32>
    decreases s.len(),
{
    if s.len() == 0 { Seq::<i32>::empty() }
    else { spec_insert(spec_sort(s.drop_last()), s.last()) }
}

pub open spec fn is_sorted_i32(s: Seq<i32>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

pub open spec fn seq_sum(s: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end { 0 }
    else { s[start] as int + seq_sum(s, start + 1, end) }
}

pub open spec fn spec_count(s: Seq<i32>, val: int) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 }
    else if s[0] as int == val {
        1 + spec_count(s.subrange(1, s.len() as int), val)
    } else {
        spec_count(s.subrange(1, s.len() as int), val)
    }
}

proof fn lemma_spec_count_bound(s: Seq<i32>, val: int)
    ensures
        spec_count(s, val) <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_spec_count_bound(s.subrange(1, s.len() as int), val);
    }
}

pub open spec fn spec_repeat(v: i32, count: int) -> Seq<i32>
    decreases (if count > 0 { count } else { 0 }),
{
    if count <= 0 { Seq::<i32>::empty() }
    else { seq![v] + spec_repeat(v, count - 1) }
}

pub open spec fn spec_from_counts(s: Seq<i32>, lo: int, hi: int) -> Seq<i32>
    decreases hi - lo,
{
    if lo >= hi { Seq::<i32>::empty() }
    else { spec_repeat(lo as i32, spec_count(s, lo)) + spec_from_counts(s, lo + 1, hi) }
}

proof fn lemma_subarray_sum_append(nums: Seq<i32>, start: int, end: int)
    requires
        0 <= start <= end < nums.len() as int,
    ensures
        subarray_sum(nums, start, end + 1) == subarray_sum(nums, start, end) + nums[end] as int,
    decreases end - start,
{
    if start < end {
        lemma_subarray_sum_append(nums, start + 1, end);
    } else {
        assert(subarray_sum(nums, start + 1, end + 1) == 0);
    }
}

proof fn lemma_subarray_sum_bounds(nums: Seq<i32>, start: int, end: int)
    requires
        0 <= start,
        start <= end,
        end <= nums.len() as int,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
    ensures
        0 <= subarray_sum(nums, start, end),
        subarray_sum(nums, start, end) <= 100 * (end - start),
        start < end ==> subarray_sum(nums, start, end) >= 1,
    decreases end - start,
{
    if start < end {
        lemma_subarray_sum_bounds(nums, start + 1, end);
    }
}

proof fn lemma_sums_from_len(nums: Seq<i32>, start: int, end: int)
    requires
        0 <= start,
        start < end,
        end <= nums.len() as int + 1,
    ensures
        sums_from(nums, start, end).len() == nums.len() as int + 1 - end,
    decreases nums.len() as int + 1 - end,
{
    if end <= nums.len() as int && end > start {
        if end + 1 <= nums.len() as int + 1 && end + 1 > start {
            lemma_sums_from_len(nums, start, end + 1);
        }
    }
}

proof fn lemma_sums_from_index(nums: Seq<i32>, start: int, end: int, idx: int)
    requires
        0 <= start,
        start < end,
        end <= nums.len() as int + 1,
        0 <= idx,
        idx < nums.len() as int + 1 - end,
    ensures
        sums_from(nums, start, end).len() > idx,
        sums_from(nums, start, end)[idx] == subarray_sum(nums, start, end + idx) as i32,
    decreases idx,
{
    lemma_sums_from_len(nums, start, end);
    if idx > 0 {
        lemma_sums_from_index(nums, start, end + 1, idx - 1);
    }
}

proof fn lemma_all_sums_len(nums: Seq<i32>, i: int)
    requires
        0 <= i <= nums.len(),
    ensures
        2 * all_sums_seq(nums, i).len() == (nums.len() - i) * (nums.len() - i + 1),
    decreases nums.len() - i,
{
    if i < nums.len() {
        lemma_sums_from_len(nums, i, i + 1);
        lemma_all_sums_len(nums, i + 1);
        let n = nums.len() - i;
        assert(all_sums_seq(nums, i).len() == sums_from(nums, i, i + 1).len() + all_sums_seq(nums, i + 1).len());
        assert(sums_from(nums, i, i + 1).len() == n);
        assert(2 * all_sums_seq(nums, i + 1).len() == (n - 1) * n);
        assert(2 * n + (n - 1) * n == n * (n + 1)) by (nonlinear_arith)
            requires n >= 1;
    } else {
        assert(all_sums_seq(nums, i) =~= Seq::<i32>::empty());
    }
}

proof fn lemma_spec_count_nonneg(s: Seq<i32>, val: int)
    ensures
        spec_count(s, val) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_spec_count_nonneg(s.subrange(1, s.len() as int), val);
    }
}

proof fn lemma_spec_count_append(s: Seq<i32>, v: i32, val: int)
    ensures
        spec_count(s.push(v), val) == spec_count(s, val) + if v as int == val { 1int } else { 0 },
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.push(v) =~= seq![v]);
        assert(seq![v].subrange(1, 1) =~= Seq::<i32>::empty());
        let empty_seq = Seq::<i32>::empty();
        assert(spec_count(empty_seq, val) == 0);
        let s1 = seq![v];
        assert(s1.subrange(1, s1.len() as int) =~= empty_seq);
        assert(spec_count(s1, val) == if v as int == val { 1int } else { 0 });
    } else {
        let sp = s.push(v);
        assert(sp.subrange(1, sp.len() as int) =~= s.subrange(1, s.len() as int).push(v));
        lemma_spec_count_append(s.subrange(1, s.len() as int), v, val);
        assert(sp[0] == s[0]);
        assert(spec_count(sp, val) == spec_count(s, val) + if v as int == val { 1int } else { 0 });
    }
}

proof fn lemma_spec_repeat_len(v: i32, count: int)
    ensures
        spec_repeat(v, count).len() == if count > 0 { count } else { 0 },
    decreases (if count > 0 { count } else { 0 }),
{
    if count > 0 {
        lemma_spec_repeat_len(v, count - 1);
    }
}

proof fn lemma_spec_repeat_index(v: i32, count: int, idx: int)
    requires
        0 <= idx < count,
    ensures
        spec_repeat(v, count).len() > idx,
        spec_repeat(v, count)[idx] == v,
    decreases (if count > 0 { count } else { 0 }),
{
    lemma_spec_repeat_len(v, count);
    if idx > 0 {
        lemma_spec_repeat_index(v, count - 1, idx - 1);
        assert(spec_repeat(v, count) =~= seq![v] + spec_repeat(v, count - 1));
    }
}

proof fn lemma_spec_insert_len(sorted: Seq<i32>, val: i32)
    ensures
        spec_insert(sorted, val).len() == sorted.len() + 1,
    decreases sorted.len(),
{
    if sorted.len() > 0 && !(val <= sorted[0]) {
        lemma_spec_insert_len(sorted.subrange(1, sorted.len() as int), val);
    }
}

proof fn lemma_spec_sort_len(s: Seq<i32>)
    ensures
        spec_sort(s).len() == s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_spec_sort_len(s.drop_last());
        lemma_spec_insert_len(spec_sort(s.drop_last()), s.last());
    }
}

proof fn lemma_is_sorted_spec_insert(sorted: Seq<i32>, val: i32)
    requires
        is_sorted_i32(sorted),
    ensures
        is_sorted_i32(spec_insert(sorted, val)),
    decreases sorted.len(),
{
    if sorted.len() == 0 {
    } else if val <= sorted[0] {
        let result = seq![val] + sorted;
        assert forall |i: int, j: int| 0 <= i <= j < result.len() implies result[i] <= result[j] by {
            if i == 0 {
                if j == 0 {
                } else {
                    assert(result[j] == sorted[j - 1]);
                    assert(sorted[0] >= val);
                    if j > 1 {
                        assert(sorted[j - 1] >= sorted[0]);
                    }
                }
            } else {
                assert(result[i] == sorted[i - 1]);
                assert(result[j] == sorted[j - 1]);
            }
        };
    } else {
        let sub = sorted.subrange(1, sorted.len() as int);
        assert(is_sorted_i32(sub)) by {
            assert forall |i: int, j: int| 0 <= i <= j < sub.len() implies sub[i] <= sub[j] by {
                assert(sorted[i + 1] <= sorted[j + 1]);
            };
        };
        lemma_is_sorted_spec_insert(sub, val);
        let ins = spec_insert(sub, val);
        let result = seq![sorted[0]] + ins;
        assert forall |i: int, j: int| 0 <= i <= j < result.len() implies result[i] <= result[j] by {
            lemma_spec_insert_len(sub, val);
            if i == 0 {
                if j == 0 {
                } else {
                    assert(is_sorted_i32(ins));
                    if ins.len() > 0 {
                        assert(ins[0] >= sorted[0]) by {
                            if sub.len() == 0 {
                            } else if val <= sub[0] {
                            } else {
                            }
                        };
                        assert(ins[j - 1] >= ins[0]);
                    }
                }
            } else {
                assert(result[i] == ins[i - 1]);
                assert(result[j] == ins[j - 1]);
                assert(ins[i - 1] <= ins[j - 1]);
            }
        };
    }
}

proof fn lemma_is_sorted_spec_sort(s: Seq<i32>)
    ensures
        is_sorted_i32(spec_sort(s)),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_is_sorted_spec_sort(s.drop_last());
        lemma_is_sorted_spec_insert(spec_sort(s.drop_last()), s.last());
    }
}

proof fn lemma_spec_insert_count(sorted: Seq<i32>, val: i32, v: int)
    ensures
        spec_count(spec_insert(sorted, val), v)
            == spec_count(sorted, v) + if val as int == v { 1int } else { 0 },
    decreases sorted.len(),
{
    if sorted.len() == 0 {
        assert(spec_insert(sorted, val) =~= seq![val]);
        assert(seq![val].subrange(1, 1) =~= Seq::<i32>::empty());
        let empty_seq = Seq::<i32>::empty();
        assert(spec_count(empty_seq, v) == 0);
        let s1 = seq![val];
        assert(s1.subrange(1, s1.len() as int) =~= empty_seq);
        assert(spec_count(s1, v) == if val as int == v { 1int } else { 0 });
    } else if val <= sorted[0] {
        let result = seq![val] + sorted;
        assert(result.subrange(1, result.len() as int) =~= sorted);
        assert(spec_count(result, v) == spec_count(sorted, v) + if val as int == v { 1int } else { 0 });
    } else {
        let sub = sorted.subrange(1, sorted.len() as int);
        lemma_spec_insert_count(sub, val, v);
        let ins = spec_insert(sub, val);
        let result = seq![sorted[0]] + ins;
        assert(result.subrange(1, result.len() as int) =~= ins);
        assert(sorted.subrange(1, sorted.len() as int) =~= sub);
        assert(spec_count(result, v) == spec_count(ins, v) + if sorted[0] as int == v { 1int } else { 0 });
        assert(spec_count(sorted, v) == spec_count(sub, v) + if sorted[0] as int == v { 1int } else { 0 });
    }
}

proof fn lemma_spec_sort_count(s: Seq<i32>, v: int)
    ensures
        spec_count(spec_sort(s), v) == spec_count(s, v),
    decreases s.len(),
{
    if s.len() > 0 {
        let prefix = s.drop_last();
        lemma_spec_sort_count(prefix, v);
        lemma_spec_insert_count(spec_sort(prefix), s.last(), v);
        lemma_spec_count_drop_last(s, v);
    }
}

proof fn lemma_spec_count_drop_last(s: Seq<i32>, v: int)
    requires
        s.len() > 0,
    ensures
        spec_count(s, v) == spec_count(s.drop_last(), v) + if s.last() as int == v { 1int } else { 0 },
    decreases s.len(),
{
    if s.len() == 1 {
        assert(s.drop_last() =~= Seq::<i32>::empty());
        assert(s.subrange(1, s.len() as int) =~= Seq::<i32>::empty());
    } else {
        let tail = s.subrange(1, s.len() as int);
        assert(tail.len() == s.len() - 1);
        assert(tail.len() > 0);
        assert(tail.drop_last() =~= s.drop_last().subrange(1, s.drop_last().len() as int));
        assert(tail.last() == s.last());
        lemma_spec_count_drop_last(tail, v);
        assert(s.drop_last().subrange(1, s.drop_last().len() as int) =~= tail.drop_last());
    }
}

proof fn lemma_sorted_same_counts_eq(s1: Seq<i32>, s2: Seq<i32>)
    requires
        is_sorted_i32(s1),
        is_sorted_i32(s2),
        s1.len() == s2.len(),
        forall |v: int| spec_count(s1, v) == spec_count(s2, v),
    ensures
        s1 =~= s2,
    decreases s1.len(),
{
    if s1.len() > 0 {
        lemma_sorted_same_counts_first(s1, s2);
        let t1 = s1.subrange(1, s1.len() as int);
        let t2 = s2.subrange(1, s2.len() as int);
        assert(is_sorted_i32(t1)) by {
            assert forall |i: int, j: int| 0 <= i <= j < t1.len() implies t1[i] <= t1[j] by {
                assert(s1[i + 1] <= s1[j + 1]);
            };
        };
        assert(is_sorted_i32(t2)) by {
            assert forall |i: int, j: int| 0 <= i <= j < t2.len() implies t2[i] <= t2[j] by {
                assert(s2[i + 1] <= s2[j + 1]);
            };
        };
        assert forall |v: int| spec_count(t1, v) == spec_count(t2, v) by {
            assert(s1.subrange(1, s1.len() as int) =~= t1);
            assert(s2.subrange(1, s2.len() as int) =~= t2);
            assert(spec_count(s1, v) == spec_count(s2, v));
            assert(spec_count(s1, v) == spec_count(t1, v) + if s1[0] as int == v { 1int } else { 0 });
            assert(spec_count(s2, v) == spec_count(t2, v) + if s2[0] as int == v { 1int } else { 0 });
        };
        lemma_sorted_same_counts_eq(t1, t2);
        assert(s1[0] == s2[0]);
        assert(t1 =~= t2);
        assert forall |i: int| 0 <= i < s1.len() implies s1[i] == s2[i] by {
            if i == 0 {
            } else {
                assert(s1[i] == t1[i - 1]);
                assert(s2[i] == t2[i - 1]);
            }
        };
        assert(s1 =~= s2);
    }
}

proof fn lemma_sorted_same_counts_first(s1: Seq<i32>, s2: Seq<i32>)
    requires
        is_sorted_i32(s1),
        is_sorted_i32(s2),
        s1.len() == s2.len(),
        s1.len() > 0,
        forall |v: int| spec_count(s1, v) == spec_count(s2, v),
    ensures
        s1[0] == s2[0],
{
    if s1[0] < s2[0] {
        lemma_sorted_no_smaller(s2, s1[0] as int);
        lemma_spec_count_first_ge_1(s1, s1[0] as int);
        assert(spec_count(s1, s1[0] as int) == spec_count(s2, s1[0] as int));
        assert(false);
    }
    if s1[0] > s2[0] {
        lemma_sorted_no_smaller(s1, s2[0] as int);
        lemma_spec_count_first_ge_1(s2, s2[0] as int);
        assert(spec_count(s1, s2[0] as int) == spec_count(s2, s2[0] as int));
        assert(false);
    }
}

proof fn lemma_sorted_no_smaller(s: Seq<i32>, val: int)
    requires
        is_sorted_i32(s),
        s.len() > 0,
        s[0] as int > val,
    ensures
        spec_count(s, val) == 0,
    decreases s.len(),
{
    assert(s[0] as int != val);
    if s.len() > 1 {
        let tail = s.subrange(1, s.len() as int);
        assert(is_sorted_i32(tail)) by {
            assert forall |i: int, j: int| 0 <= i <= j < tail.len() implies tail[i] <= tail[j] by {
                assert(s[i + 1] <= s[j + 1]);
            };
        };
        assert(tail[0] == s[1]);
        assert(s[1] >= s[0]);
        assert(tail[0] as int > val);
        lemma_sorted_no_smaller(tail, val);
        assert(spec_count(tail, val) == 0);
    }
    assert(spec_count(s, val) == spec_count(s.subrange(1, s.len() as int), val));
}

proof fn lemma_spec_count_first_ge_1(s: Seq<i32>, val: int)
    requires
        s.len() > 0,
        s[0] as int == val,
    ensures
        spec_count(s, val) >= 1,
{
    lemma_spec_count_nonneg(s.subrange(1, s.len() as int), val);
}

proof fn lemma_spec_from_counts_sorted(s: Seq<i32>, lo: int, hi: int)
    requires
        0 <= lo,
        hi <= 100005,
    ensures
        is_sorted_i32(spec_from_counts(s, lo, hi)),
    decreases hi - lo,
{
    if lo < hi {
        lemma_spec_from_counts_sorted(s, lo + 1, hi);
        let head = spec_repeat(lo as i32, spec_count(s, lo));
        let tail = spec_from_counts(s, lo + 1, hi);
        let result = head + tail;
        lemma_spec_repeat_len(lo as i32, spec_count(s, lo));
        lemma_spec_count_nonneg(s, lo);
        assert forall |i: int, j: int| 0 <= i <= j < result.len() implies result[i] <= result[j] by {
            if i < head.len() && j < head.len() {
                lemma_spec_repeat_index(lo as i32, spec_count(s, lo), i);
                lemma_spec_repeat_index(lo as i32, spec_count(s, lo), j);
            } else if i < head.len() && j >= head.len() {
                lemma_spec_repeat_index(lo as i32, spec_count(s, lo), i);
                assert(result[j] == tail[j - head.len()]);
                lemma_spec_from_counts_lower_bound(s, lo + 1, hi, j - head.len());
            } else {
                assert(result[i] == tail[i - head.len()]);
                assert(result[j] == tail[j - head.len()]);
                assert(is_sorted_i32(tail));
            }
        };
    }
}

proof fn lemma_spec_from_counts_lower_bound(s: Seq<i32>, lo: int, hi: int, idx: int)
    requires
        0 <= lo,
        hi <= 100005,
        lo <= hi,
        0 <= idx < spec_from_counts(s, lo, hi).len(),
    ensures
        spec_from_counts(s, lo, hi)[idx] as int >= lo,
    decreases hi - lo,
{
    if lo < hi {
        let head = spec_repeat(lo as i32, spec_count(s, lo));
        let tail = spec_from_counts(s, lo + 1, hi);
        lemma_spec_repeat_len(lo as i32, spec_count(s, lo));
        lemma_spec_count_nonneg(s, lo);
        if idx < head.len() {
            lemma_spec_repeat_index(lo as i32, spec_count(s, lo), idx);
            assert(spec_from_counts(s, lo, hi) =~= head + tail);
            assert(spec_from_counts(s, lo, hi)[idx] == head[idx]);
        } else {
            lemma_spec_from_counts_lower_bound(s, lo + 1, hi, idx - head.len());
            assert(spec_from_counts(s, lo, hi) =~= head + tail);
            assert(spec_from_counts(s, lo, hi)[idx] == tail[idx - head.len()]);
            assert(tail[idx - head.len()] as int >= lo + 1);
            assert(tail[idx - head.len()] as int >= lo);
        }
    }
}

proof fn lemma_spec_from_counts_len(s: Seq<i32>, lo: int, hi: int)
    requires
        0 <= lo,
        hi <= 100005,
        lo <= hi,
        forall |v: int| !(lo <= v < hi) ==> spec_count(s, v) == 0,
    ensures
        spec_from_counts(s, lo, hi).len() == s.len(),
    decreases hi - lo,
{
    lemma_sum_counts_eq_len(s, lo, hi);
    lemma_spec_from_counts_len_aux(s, lo, hi);
    if lo < hi {
        lemma_spec_count_nonneg(s, lo);
        lemma_spec_repeat_len(lo as i32, spec_count(s, lo));
    }
}

pub open spec fn sum_counts(s: Seq<i32>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if lo >= hi { 0 }
    else { spec_count(s, lo) + sum_counts(s, lo + 1, hi) }
}

proof fn lemma_sum_counts_eq_len(s: Seq<i32>, lo: int, hi: int)
    requires
        lo <= hi,
        forall |v: int| !(lo <= v < hi) ==> spec_count(s, v) == 0,
    ensures
        sum_counts(s, lo, hi) == s.len(),
    decreases s.len(),
{
    if s.len() == 0 {
        lemma_sum_counts_zero(s, lo, hi);
    } else {
        let val = s[0] as int;
        let tail = s.subrange(1, s.len() as int);
        assert(lo <= val < hi) by {
            lemma_spec_count_first_ge_1(s, val);
            if !(lo <= val && val < hi) {
                assert(spec_count(s, val) == 0);
                assert(false);
            }
        };
        assert forall |v: int| !(lo <= v < hi) implies spec_count(tail, v) == 0 by {
            assert(s.subrange(1, s.len() as int) =~= tail);
            if !(lo <= v && v < hi) {
                assert(spec_count(s, v) == 0);
                lemma_spec_count_nonneg(tail, v);
                if s[0] as int == v {
                    assert(false);
                }
            }
        };
        lemma_sum_counts_eq_len(tail, lo, hi);
        lemma_sum_counts_increment(s, tail, lo, hi, val);
    }
}

proof fn lemma_sum_counts_zero(s: Seq<i32>, lo: int, hi: int)
    requires
        s.len() == 0,
        lo <= hi,
    ensures
        sum_counts(s, lo, hi) == 0,
    decreases hi - lo,
{
    if lo < hi {
        lemma_sum_counts_zero(s, lo + 1, hi);
    }
}

proof fn lemma_sum_counts_increment(s: Seq<i32>, tail: Seq<i32>, lo: int, hi: int, val: int)
    requires
        s.len() > 0,
        tail =~= s.subrange(1, s.len() as int),
        lo <= val < hi,
        s[0] as int == val,
    ensures
        sum_counts(s, lo, hi) == sum_counts(tail, lo, hi) + 1,
    decreases hi - lo,
{
    if lo < hi {
        if lo == val {
            lemma_sum_counts_same_tail(s, tail, lo + 1, hi, val);
        } else {
            lemma_sum_counts_increment(s, tail, lo + 1, hi, val);
        }
    }
}

proof fn lemma_sum_counts_same_tail(s: Seq<i32>, tail: Seq<i32>, lo: int, hi: int, val: int)
    requires
        s.len() > 0,
        tail =~= s.subrange(1, s.len() as int),
        s[0] as int == val,
        !(lo <= val < hi),
    ensures
        sum_counts(s, lo, hi) == sum_counts(tail, lo, hi),
    decreases hi - lo,
{
    if lo < hi {
        assert(s[0] as int != lo) by {
            if lo <= val && val < hi {
                assert(false);
            }
        };
        assert(s.subrange(1, s.len() as int) =~= tail);
        lemma_sum_counts_same_tail(s, tail, lo + 1, hi, val);
    }
}

proof fn lemma_spec_from_counts_len_aux(s: Seq<i32>, lo: int, hi: int)
    requires
        0 <= lo,
        hi <= 100005,
        lo <= hi,
    ensures
        spec_from_counts(s, lo, hi).len() == sum_counts(s, lo, hi),
    decreases hi - lo,
{
    if lo < hi {
        lemma_spec_count_nonneg(s, lo);
        lemma_spec_repeat_len(lo as i32, spec_count(s, lo));
        lemma_spec_from_counts_len_aux(s, lo + 1, hi);
    }
}

proof fn lemma_spec_from_counts_count(s: Seq<i32>, lo: int, hi: int, v: int)
    requires
        0 <= lo,
        hi <= 100005,
        lo <= hi,
    ensures
        spec_count(spec_from_counts(s, lo, hi), v) ==
            if lo <= v && v < hi { spec_count(s, v) } else { 0int },
    decreases hi - lo,
{
    if lo < hi {
        lemma_spec_count_nonneg(s, lo);
        lemma_spec_repeat_len(lo as i32, spec_count(s, lo));
        let head = spec_repeat(lo as i32, spec_count(s, lo));
        let tail = spec_from_counts(s, lo + 1, hi);
        let result = head + tail;
        assert(spec_from_counts(s, lo, hi) =~= result);
        lemma_spec_count_concat(head, tail, v);
        lemma_spec_repeat_count(lo as i32, spec_count(s, lo), v);
        lemma_spec_from_counts_count(s, lo + 1, hi, v);
    }
}

proof fn lemma_spec_count_concat(s1: Seq<i32>, s2: Seq<i32>, v: int)
    ensures
        spec_count(s1 + s2, v) == spec_count(s1, v) + spec_count(s2, v),
    decreases s1.len(),
{
    if s1.len() == 0 {
        assert(s1 + s2 =~= s2);
    } else {
        let concat = s1 + s2;
        let tail1 = s1.subrange(1, s1.len() as int);
        assert(concat.subrange(1, concat.len() as int) =~= tail1 + s2);
        lemma_spec_count_concat(tail1, s2, v);
    }
}

proof fn lemma_spec_repeat_count(v: i32, count: int, val: int)
    requires
        count >= 0,
    ensures
        spec_count(spec_repeat(v, count), val) == if v as int == val { count } else { 0int },
    decreases count,
{
    if count > 0 {
        let s = spec_repeat(v, count);
        assert(s =~= seq![v] + spec_repeat(v, count - 1));
        assert(s.subrange(1, s.len() as int) =~= spec_repeat(v, count - 1));
        lemma_spec_repeat_count(v, count - 1, val);
    }
}

proof fn lemma_counting_sort_correct(s: Seq<i32>, lo: int, hi: int)
    requires
        0 <= lo,
        hi <= 100005,
        lo <= hi,
        forall |k: int| 0 <= k < s.len() ==> lo <= (s[k] as int),
        forall |k: int| 0 <= k < s.len() ==> (s[k] as int) < hi,
    ensures
        spec_from_counts(s, lo, hi) =~= spec_sort(s)
{
    lemma_spec_from_counts_sorted(s, lo, hi);
    lemma_is_sorted_spec_sort(s);

    assert forall |v: int| !(lo <= v < hi) implies spec_count(s, v) == 0 by {
        lemma_spec_count_outside_range(s, lo, hi, v);
    };
    lemma_spec_from_counts_len(s, lo, hi);
    lemma_spec_sort_len(s);

    assert forall |v: int| spec_count(spec_from_counts(s, lo, hi), v) == spec_count(spec_sort(s), v) by {
        lemma_spec_from_counts_count(s, lo, hi, v);
        lemma_spec_sort_count(s, v);
        if lo <= v && v < hi {
        } else {
            lemma_spec_count_outside_range(s, lo, hi, v);
        }
    };

    lemma_sorted_same_counts_eq(spec_from_counts(s, lo, hi), spec_sort(s));
}

proof fn lemma_spec_count_outside_range(s: Seq<i32>, lo: int, hi: int, v: int)
    requires
        !(lo <= v && v < hi),
        forall |k: int| 0 <= k < s.len() ==> lo <= (s[k] as int),
        forall |k: int| 0 <= k < s.len() ==> (s[k] as int) < hi,
    ensures
        spec_count(s, v) == 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_spec_count_outside_range(s.subrange(1, s.len() as int), lo, hi, v);
        assert(s[0] as int != v) by {
            assert(lo <= s[0] as int);
            assert((s[0] as int) < hi);
        };
    }
}

proof fn lemma_seq_sum_append(s: Seq<i32>, start: int, end: int)
    requires
        0 <= start,
        start <= end,
        end < s.len(),
    ensures
        seq_sum(s, start, end + 1) == seq_sum(s, start, end) + s[end] as int,
    decreases end - start,
{
    if start < end {
        lemma_seq_sum_append(s, start + 1, end);
    } else {
        assert(seq_sum(s, start + 1, end + 1) == 0);
    }
}

proof fn lemma_mod_property(a: int, b: int, m: int)
    requires
        m > 0,
        0 <= a,
        0 <= b,
    ensures
        (a % m + b) % m == (a + b) % m,
{
    vstd::arithmetic::div_mod::lemma_add_mod_noop_right(b, a, m);
}

proof fn lemma_n_n_1_bound(n: int)
    requires 0 <= n <= 1000,
    ensures n * (n + 1) <= 1001000,
{
    assert(n * (n + 1) <= 1001000) by (nonlinear_arith)
        requires 0 <= n <= 1000;
}

proof fn lemma_seq_sum_nonneg(s: Seq<i32>, start: int, end: int)
    requires
        0 <= start,
        end <= s.len(),
        forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 1i32,
    ensures
        seq_sum(s, start, end) >= 0,
    decreases end - start,
{
    if start < end {
        lemma_seq_sum_nonneg(s, start + 1, end);
    }
}

impl Solution {
    pub fn range_sum(nums: Vec<i32>, n: i32, left: i32, right: i32) -> (result: i32)
        requires
            n == nums@.len(),
            1 <= nums@.len() <= 1000,
            forall |i: int| 0 <= i < nums@.len() ==> 1 <= #[trigger] nums@[i] <= 100,
            1 <= left <= right <= n * (n + 1) / 2,
        ensures
            result as int == seq_sum(
                spec_sort(all_sums_seq(nums@, 0)),
                (left - 1) as int, right as int,
            ) % 1_000_000_007,
    {
        let len: usize = n as usize;
        let mut sums: Vec<i32> = Vec::new();
        let mut i: usize = 0;

        while i < len
            invariant
                0 <= i <= len,
                len == nums@.len(),
                1 <= nums@.len() <= 1000,
                forall |k: int| 0 <= k < nums@.len() ==> 1 <= #[trigger] nums@[k] <= 100,
                sums@ + all_sums_seq(nums@, i as int) =~= all_sums_seq(nums@, 0),
                forall |k: int| 0 <= k < sums@.len() ==> 1 <= #[trigger] sums@[k] <= 100000,
            decreases len - i,
        {
            let mut sum: i32 = 0;
            let mut j: usize = i;
            let ghost sums_outer = sums@;
            let ghost sums_outer_len = sums@.len();

            while j < len
                invariant
                    i <= j <= len,
                    len == nums@.len(),
                    1 <= nums@.len() <= 1000,
                    forall |k: int| 0 <= k < nums@.len() ==> 1 <= #[trigger] nums@[k] <= 100,
                    sum as int == subarray_sum(nums@, i as int, j as int),
                    0 <= sum <= 100000,
                    sums@.len() == sums_outer_len + (j - i) as int,
                    sums@.subrange(0, sums_outer_len as int) =~= sums_outer,
                    forall |k: int| 0 <= k < (j - i) as int ==>
                        #[trigger] sums@[sums_outer_len + k] == subarray_sum(nums@, i as int, (i as int) + k + 1) as i32,
                    sums_outer + all_sums_seq(nums@, i as int) =~= all_sums_seq(nums@, 0),
                    sums_outer_len == sums_outer.len(),
                    forall |k: int| 0 <= k < sums@.len() ==> 1 <= #[trigger] sums@[k] <= 100000,
                decreases len - j,
            {
                proof {
                    lemma_subarray_sum_append(nums@, i as int, j as int);
                    lemma_subarray_sum_bounds(nums@, i as int, (j + 1) as int);
                }
                sum = sum + nums[j];
                proof {
                    assert(sum as int == subarray_sum(nums@, i as int, (j + 1) as int));
                    assert(1 <= sum <= 100000);
                }
                sums.push(sum);
                proof {
                    assert(sums@.len() == sums_outer_len + (j + 1 - i) as int);
                    assert(sums@.subrange(0, sums_outer_len as int) =~= sums_outer);
                    assert forall |k: int| 0 <= k < (j + 1 - i) as int implies
                        #[trigger] sums@[sums_outer_len + k] == subarray_sum(nums@, i as int, (i as int) + k + 1) as i32
                    by {
                        if k < (j - i) as int {
                        } else {
                            assert(k == (j - i) as int);
                            assert(sums@[sums_outer_len + k] == sum);
                        }
                    };
                }
                j = j + 1;
            }

            proof {
                lemma_sums_from_len(nums@, i as int, (i + 1) as int);
                let sf = sums_from(nums@, i as int, (i + 1) as int);
                let appended_len = (len - i) as int;

                assert(sums@.len() == sums_outer_len + appended_len);
                assert(sf.len() == appended_len);
                assert((sums_outer + sf).len() == sums_outer_len + appended_len);

                assert forall |k: int| 0 <= k < sums@.len() implies
                    sums@[k] == (sums_outer + sf)[k]
                by {
                    if k < sums_outer_len {
                        assert(sums@[k] == sums_outer[k]);
                        assert((sums_outer + sf)[k] == sums_outer[k]);
                    } else {
                        let idx = k - sums_outer_len;
                        lemma_sums_from_index(nums@, i as int, (i + 1) as int, idx);
                        lemma_subarray_sum_bounds(nums@, i as int, (i as int) + idx + 1);
                        assert(sums_outer_len + idx == k);
                        assert(sums@[sums_outer_len + idx] == subarray_sum(nums@, i as int, (i as int) + idx + 1) as i32);
                        assert(sf[idx] == subarray_sum(nums@, i as int, (i + 1) as int + idx) as i32);
                        assert((i as int) + idx + 1 == (i + 1) as int + idx);
                        assert((sums_outer + sf)[k] == sf[idx]);
                    }
                };
                assert(sums@ =~= sums_outer + sf);

                assert(all_sums_seq(nums@, i as int) =~= sf + all_sums_seq(nums@, (i + 1) as int));
                assert(sums_outer + all_sums_seq(nums@, i as int) =~= all_sums_seq(nums@, 0));
                assert((sums_outer + sf) + all_sums_seq(nums@, (i + 1) as int)
                    =~= sums_outer + (sf + all_sums_seq(nums@, (i + 1) as int)));
                assert(sums@ + all_sums_seq(nums@, (i + 1) as int) =~= all_sums_seq(nums@, 0));
            }

            i = i + 1;
        }

        proof {
            assert(all_sums_seq(nums@, len as int) =~= Seq::<i32>::empty());
            assert(sums@ + Seq::<i32>::empty() =~= sums@);
            assert(sums@ =~= all_sums_seq(nums@, 0));
        }

        let ghost original_sums = sums@;
        let m: usize = sums.len();

        let max_val: usize = 100001;
        let mut counts: Vec<i32> = Vec::new();
        let mut ci: usize = 0;
        while ci < max_val
            invariant
                0 <= ci <= max_val,
                max_val == 100001,
                counts@.len() == ci as int,
                forall |k: int| 0 <= k < ci as int ==> #[trigger] counts@[k] == 0i32,
            decreases max_val - ci,
        {
            counts.push(0i32);
            ci = ci + 1;
        }

        let mut si: usize = 0;
        while si < m
            invariant
                0 <= si <= m,
                m == sums@.len(),
                counts@.len() == max_val as int,
                max_val == 100001,
                sums@ =~= original_sums,
                nums@.len() <= 1000,
                sums@ =~= all_sums_seq(nums@, 0),
                forall |k: int| 0 <= k < sums@.len() ==> 1 <= #[trigger] sums@[k] <= 100000,
                forall |v: int| 0 <= v < max_val as int ==>
                    #[trigger] counts@[v] as int == spec_count(sums@.subrange(0, si as int), v),
                forall |v: int| 0 <= v < max_val as int ==> #[trigger] counts@[v] >= 0i32,
            decreases m - si,
        {
            let v: usize = sums[si] as usize;
            proof {
                assert(1 <= sums@[si as int] <= 100000);
                assert(1 <= v <= 100000);
                let old_sub = sums@.subrange(0, si as int);
                let new_sub = sums@.subrange(0, (si + 1) as int);
                assert(new_sub =~= old_sub.push(sums@[si as int]));
                assert forall |w: int| 0 <= w < max_val as int && w != v as int implies
                    #[trigger] counts@[w] as int == spec_count(new_sub, w)
                by {
                    lemma_spec_count_append(old_sub, sums@[si as int], w);
                    assert(sums@[si as int] as int != w);
                };
                lemma_spec_count_append(old_sub, sums@[si as int], v as int);
            }
            proof {
                lemma_spec_count_bound(sums@.subrange(0, si as int), v as int);
                assert(counts@[v as int] as int <= sums@.subrange(0, si as int).len());
                assert(sums@.subrange(0, si as int).len() == si as int);
                assert(si as int <= m as int);
                lemma_all_sums_len(nums@, 0);
                lemma_n_n_1_bound(nums@.len() as int);
                assert(all_sums_seq(nums@, 0).len() <= 500500);
                assert(m <= 500500);
                assert(counts@[v as int] + 1 <= 500501);
            }
            counts.set(v, counts[v] + 1);
            si = si + 1;
        }

        let mut sorted: Vec<i32> = Vec::new();
        let mut vi: usize = 0;

        proof {
            assert(sums@.subrange(0, m as int) =~= sums@);
        }

        while vi < max_val
            invariant
                0 <= vi <= max_val,
                max_val == 100001,
                counts@.len() == max_val as int,
                sums@ =~= original_sums,
                nums@.len() <= 1000,
                sums@ =~= all_sums_seq(nums@, 0),
                forall |k: int| 0 <= k < sums@.len() ==> 1 <= #[trigger] sums@[k] <= 100000,
                forall |v: int| 0 <= v < max_val as int ==>
                    #[trigger] counts@[v] as int == spec_count(sums@, v),
                sorted@ =~= spec_from_counts(sums@, 0, vi as int),
                forall |k: int| 0 <= k < sorted@.len() ==> 1 <= #[trigger] sorted@[k] <= 100000,
                forall |v: int| 0 <= v < max_val as int ==> #[trigger] counts@[v] >= 0i32,
                m == sums@.len(),
            decreases max_val - vi,
        {
            let mut c: i32 = 0;
            let ghost sorted_before = sorted@;
            while c < counts[vi]
                invariant
                    0 <= c <= counts@[vi as int],
                    0 <= vi < max_val,
                    max_val == 100001,
                    counts@.len() == max_val as int,
                    forall |v: int| 0 <= v < max_val as int ==>
                        #[trigger] counts@[v] as int == spec_count(sums@, v),
                    sorted@ =~= sorted_before + spec_repeat(vi as i32, c as int),
                    sorted_before =~= spec_from_counts(sums@, 0, vi as int),
                    forall |k: int| 0 <= k < sorted@.len() ==> 1 <= #[trigger] sorted@[k] <= 100000,
                    forall |v: int| 0 <= v < max_val as int ==> #[trigger] counts@[v] >= 0i32,
                    sums@ =~= original_sums,
                    forall |k: int| 0 <= k < sums@.len() ==> 1 <= #[trigger] sums@[k] <= 100000,
                decreases counts@[vi as int] - c,
            {
                sorted.push(vi as i32);
                proof {
                    lemma_spec_repeat_len(vi as i32, c as int);
                    lemma_spec_repeat_len(vi as i32, (c + 1) as int);
                    assert(spec_repeat(vi as i32, (c + 1) as int) =~= seq![vi as i32] + spec_repeat(vi as i32, c as int));
                    lemma_spec_repeat_push(vi as i32, c as int);
                    assert(sorted@ =~= sorted_before + spec_repeat(vi as i32, (c + 1) as int));
                    assert(1 <= vi as i32 <= 100000) by {
                        if vi == 0 {
                            assert(spec_count(sums@, 0) == counts@[0] as int);
                            assert(c < counts@[0]);
                            lemma_spec_count_outside_range(sums@, 1, 100001, 0);
                            assert(false);
                        }
                    };
                }
                c = c + 1;
            }
            proof {
                lemma_spec_from_counts_split_last(sums@, 0, vi as int + 1);
                assert(counts@[vi as int] as int == spec_count(sums@, vi as int));
                assert(sorted@ =~= spec_from_counts(sums@, 0, vi as int) + spec_repeat(vi as i32, counts@[vi as int] as int));
                assert(sorted@ =~= spec_from_counts(sums@, 0, (vi + 1) as int));
            }
            vi = vi + 1;
        }

        proof {
            assert(sorted@ =~= spec_from_counts(sums@, 0, max_val as int));
            assert forall |k: int| 0 <= k < sums@.len() implies 1 <= #[trigger] sums@[k] as int by {};
            assert forall |k: int| 0 <= k < sums@.len() implies (#[trigger] sums@[k] as int) < 100001 by {};
            lemma_counting_sort_correct(sums@, 0, 100001);
            assert(spec_from_counts(sums@, 0, 100001) =~= spec_sort(sums@));
            assert(sorted@ =~= spec_sort(sums@));
            assert(sums@ =~= all_sums_seq(nums@, 0));
            assert(sorted@ =~= spec_sort(all_sums_seq(nums@, 0)));
        }

        let modv: i64 = 1_000_000_007;
        let mut result: i64 = 0;
        let mut k: usize = (left - 1) as usize;

        proof {
            assert(m == sums@.len());
            lemma_spec_sort_len(all_sums_seq(nums@, 0));
            assert(spec_sort(all_sums_seq(nums@, 0)).len() == all_sums_seq(nums@, 0).len());
            lemma_all_sums_len(nums@, 0);
            assert(2 * all_sums_seq(nums@, 0).len() == (nums@.len() - 0) * (nums@.len() - 0 + 1));
            assert(2 * all_sums_seq(nums@, 0).len() == nums@.len() * (nums@.len() + 1));
            lemma_n_n_1_bound(nums@.len() as int);
            assert(all_sums_seq(nums@, 0).len() <= 500500);
            assert(right <= n * (n + 1) / 2);
            assert(2 * (right as int) <= (n as int) * ((n as int) + 1)) by (nonlinear_arith)
                requires right <= n * (n + 1) / 2, n >= 1;
            assert((right as usize) <= sorted.len());
        }

        while k < right as usize
            invariant
                (left - 1) as usize <= k <= right as usize,
                k <= sorted@.len(),
                0 <= result < modv,
                modv == 1_000_000_007,
                result as int == seq_sum(sorted@, (left - 1) as int, k as int) % modv as int,
                sorted@ =~= spec_sort(all_sums_seq(nums@, 0)),
                forall |kk: int| 0 <= kk < sorted@.len() ==> 1 <= #[trigger] sorted@[kk] <= 100000,
                1 <= left <= right,
                right as usize <= sorted@.len(),
            decreases right as usize - k,
        {
            proof {
                lemma_seq_sum_append(sorted@, (left - 1) as int, k as int);
                assert(seq_sum(sorted@, (left - 1) as int, (k + 1) as int)
                    == seq_sum(sorted@, (left - 1) as int, k as int) + sorted@[k as int] as int);
                assert(sorted@[k as int] >= 1);
                assert(sorted@[k as int] <= 100000);
                assert(result >= 0);
                assert(result < modv);
                lemma_seq_sum_nonneg(sorted@, (left - 1) as int, k as int);
                lemma_mod_property(
                    seq_sum(sorted@, (left - 1) as int, k as int),
                    sorted@[k as int] as int,
                    modv as int,
                );
            }
            result = (result + sorted[k] as i64) % modv;
            k = k + 1;
        }

        result as i32
    }
}

proof fn lemma_spec_repeat_push(v: i32, count: int)
    requires
        count >= 0,
    ensures
        spec_repeat(v, count).push(v) =~= spec_repeat(v, count + 1),
    decreases count,
{
    if count == 0 {
        assert(spec_repeat(v, 0) =~= Seq::<i32>::empty());
        assert(Seq::<i32>::empty().push(v) =~= seq![v]);
        assert(spec_repeat(v, 1) =~= seq![v] + spec_repeat(v, 0));
        assert(seq![v] + Seq::<i32>::empty() =~= seq![v]);
    } else {
        lemma_spec_repeat_push(v, count - 1);
        let s = spec_repeat(v, count);
        assert(s =~= seq![v] + spec_repeat(v, count - 1));
        let tail = spec_repeat(v, count - 1);
        assert(s.push(v) =~= (seq![v] + tail).push(v));
        assert((seq![v] + tail).push(v) =~= seq![v] + tail.push(v));
        assert(tail.push(v) =~= spec_repeat(v, count));
        assert(seq![v] + spec_repeat(v, count) =~= spec_repeat(v, count + 1));
    }
}

proof fn lemma_spec_from_counts_split_last(s: Seq<i32>, lo: int, hi: int)
    requires
        lo < hi,
    ensures
        spec_from_counts(s, lo, hi) =~= spec_from_counts(s, lo, hi - 1) + spec_repeat((hi - 1) as i32, spec_count(s, hi - 1)),
    decreases hi - lo,
{
    if lo == hi - 1 {
        assert(spec_from_counts(s, lo, hi - 1) =~= Seq::<i32>::empty());
        assert(spec_from_counts(s, lo + 1, hi) =~= Seq::<i32>::empty());
        lemma_spec_count_nonneg(s, lo);
        lemma_spec_repeat_len(lo as i32, spec_count(s, lo));
        assert(spec_from_counts(s, lo, hi) =~= spec_repeat(lo as i32, spec_count(s, lo)) + Seq::<i32>::empty());
        assert(spec_repeat(lo as i32, spec_count(s, lo)) + Seq::<i32>::empty() =~= spec_repeat(lo as i32, spec_count(s, lo)));
    } else {
        lemma_spec_from_counts_split_last(s, lo + 1, hi);
        lemma_spec_count_nonneg(s, lo);
        lemma_spec_repeat_len(lo as i32, spec_count(s, lo));
        let a = spec_repeat(lo as i32, spec_count(s, lo));
        let b = spec_from_counts(s, lo + 1, hi - 1);
        let c = spec_repeat((hi - 1) as i32, spec_count(s, hi - 1));
        assert(spec_from_counts(s, lo + 1, hi) =~= b + c);
        assert(spec_from_counts(s, lo, hi) =~= a + (b + c));
        assert(a + (b + c) =~= (a + b) + c);
        assert(spec_from_counts(s, lo, hi - 1) =~= a + b);
    }
}

}
