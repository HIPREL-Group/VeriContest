use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_ones_spec(n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        (n % 2) + count_ones_spec(n / 2)
    }
}

pub open spec fn bit_le(a: int, b: int) -> bool {
    count_ones_spec(a) < count_ones_spec(b)
    || (count_ones_spec(a) == count_ones_spec(b) && a <= b)
}

pub open spec fn sorted_by_bits(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> bit_le(s[i] as int, s[j] as int)
}

pub open spec fn count_occ(s: Seq<i32>, v: i32) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] == v { 1int } else { 0int }) + count_occ(s.subrange(1, s.len() as int), v)
    }
}

pub open spec fn count_occ_in_range(s: Seq<i32>, v: i32, start: int, end: int) -> int
    decreases end - start when start <= end
{
    if start >= end {
        0
    } else {
        (if s[start] == v { 1int } else { 0int }) + count_occ_in_range(s, v, start + 1, end)
    }
}

pub open spec fn is_permutation(a: Seq<i32>, b: Seq<i32>) -> bool {
    a.len() == b.len() && forall|v: i32| count_occ(a, v) == count_occ(b, v)
}

proof fn count_ones_bounds(n: int)
    requires n >= 0,
    ensures 0 <= count_ones_spec(n) <= n,
    decreases n,
{
    if n > 0 {
        count_ones_bounds(n / 2);
    }
}

proof fn bit_le_transitive(a: int, b: int, c: int)
    requires
        bit_le(a, b),
        bit_le(b, c),
    ensures
        bit_le(a, c),
{
}

proof fn count_occ_in_range_subrange(s: Seq<i32>, v: i32, a: int, b: int)
    requires
        0 <= a <= b <= s.len(),
    ensures
        count_occ_in_range(s, v, a, b) == count_occ_in_range(s.subrange(a, b), v, 0, b - a),
    decreases b - a,
{
    if a < b {
        let sub = s.subrange(a, b);
        count_occ_in_range_subrange(s, v, a + 1, b);
        assert(s.subrange(a + 1, b) =~= sub.subrange(1, sub.len() as int));
        count_occ_in_range_subrange(sub, v, 1, sub.len() as int);
    }
}

proof fn count_occ_equals_in_range(s: Seq<i32>, v: i32)
    ensures
        count_occ(s, v) == count_occ_in_range(s, v, 0, s.len() as int),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.subrange(0, 0) =~= Seq::<i32>::empty());
    } else {
        let sub = s.subrange(1, s.len() as int);
        count_occ_equals_in_range(sub, v);
        count_occ_in_range_subrange(s, v, 1, s.len() as int);
    }
}

proof fn count_occ_in_range_additive(s: Seq<i32>, v: i32, a: int, b: int, c: int)
    requires
        a <= b <= c,
    ensures
        count_occ_in_range(s, v, a, c) == count_occ_in_range(s, v, a, b) + count_occ_in_range(s, v, b, c),
    decreases b - a,
{
    if a < b {
        count_occ_in_range_additive(s, v, a + 1, b, c);
    }
}

proof fn count_occ_in_range_same_elements(s1: Seq<i32>, s2: Seq<i32>, v: i32, start: int, end: int)
    requires
        s1.len() == s2.len(),
        start <= end <= s1.len(),
        forall|k: int| start <= k < end ==> s1[k] == s2[k],
    ensures
        count_occ_in_range(s1, v, start, end) == count_occ_in_range(s2, v, start, end),
    decreases end - start,
{
    if start < end {
        count_occ_in_range_same_elements(s1, s2, v, start + 1, end);
    }
}

proof fn swap_preserves_count(before: Seq<i32>, after: Seq<i32>, v: i32, i: int, j: int)
    requires
        before.len() == after.len(),
        0 <= i <= j < before.len(),
        after[i] == before[j],
        after[j] == before[i],
        forall|k: int| 0 <= k < before.len() && k != i && k != j ==> after[k] == before[k],
    ensures
        count_occ_in_range(before, v, 0, before.len() as int) ==
            count_occ_in_range(after, v, 0, after.len() as int),
{
    if i == j {
        count_occ_in_range_same_elements(before, after, v, 0, before.len() as int);
    } else {
        count_occ_in_range_additive(before, v, 0, i, before.len() as int);
        count_occ_in_range_additive(before, v, i, j, before.len() as int);
        count_occ_in_range_additive(after, v, 0, i, after.len() as int);
        count_occ_in_range_additive(after, v, i, j, after.len() as int);
        count_occ_in_range_same_elements(before, after, v, 0, i);
        count_occ_in_range_same_elements(before, after, v, i + 1, j);
        count_occ_in_range_same_elements(before, after, v, j + 1, before.len() as int);
    }
}

impl Solution {
    fn count_ones(n: i32) -> (result: i32)
        requires
            0 <= n <= 10000,
        ensures
            result as int == count_ones_spec(n as int),
    {
        proof { count_ones_bounds(n as int); }
        let mut count: i32 = 0;
        let mut val: i32 = n;
        while val > 0
            invariant
                0 <= n <= 10000,
                0 <= val <= n,
                count_ones_spec(n as int) <= n as int,
                0 <= count <= n,
                count as int + count_ones_spec(val as int) == count_ones_spec(n as int),
            decreases val,
        {
            proof { count_ones_bounds(val as int / 2); }
            count = count + (val % 2);
            val = val / 2;
        }
        count
    }

    pub fn sort_by_bits(arr: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= arr.len() <= 500,
            forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 10000,
        ensures
            result.len() == arr.len(),
            sorted_by_bits(result@),
            is_permutation(arr@, result@),
    {
        let ghost original = arr@;
        let mut result = arr;
        let n = result.len();
        let mut i: usize = 0;
        while i < n
            invariant
                n == result.len(),
                n <= 500,
                0 <= i <= n,
                original.len() == n,
                forall|a: int, b: int| 0 <= a < b < i as int
                    ==> bit_le(result[a] as int, result[b] as int),
                forall|a: int, b: int| 0 <= a < i as int && i as int <= b < n as int
                    ==> bit_le(result[a] as int, result[b] as int),
                forall|v: i32| count_occ(original, v) == count_occ(result@, v),
                forall|k: int| 0 <= k < n as int ==> 0 <= #[trigger] result[k] <= 10000,
            decreases n - i,
        {
            let mut min_idx: usize = i;
            let mut j: usize = i + 1;
            while j < n
                invariant
                    n == result.len(),
                    i < n,
                    i as int <= min_idx as int,
                    min_idx < j,
                    j <= n,
                    forall|k: int| i as int <= k < j as int
                        ==> bit_le(result[min_idx as int] as int, result[k] as int),
                    forall|k: int| 0 <= k < n as int ==> 0 <= #[trigger] result[k] <= 10000,
                decreases n - j,
            {
                let ones_j = Self::count_ones(result[j]);
                let ones_min = Self::count_ones(result[min_idx]);
                if ones_j < ones_min || (ones_j == ones_min && result[j] < result[min_idx]) {
                    proof {
                        assert(bit_le(result[j as int] as int, result[min_idx as int] as int));
                        assert forall|k: int| i as int <= k < j as int + 1
                            implies bit_le(result[j as int] as int, result[k] as int) by {
                            if k == j as int {
                            } else {
                                bit_le_transitive(
                                    result[j as int] as int,
                                    result[min_idx as int] as int,
                                    result[k] as int,
                                );
                            }
                        };
                    }
                    min_idx = j;
                }
                j = j + 1;
            }
            let ghost before = result@;
            let temp = result[i];
            let val_at_min = result[min_idx];
            result.set(i, val_at_min);
            result.set(min_idx, temp);
            proof {
                assert forall|v: i32| count_occ(original, v) == count_occ(result@, v) by {
                    count_occ_equals_in_range(before, v);
                    count_occ_equals_in_range(result@, v);
                    swap_preserves_count(before, result@, v, i as int, min_idx as int);
                };
                assert forall|a: int, b: int| 0 <= a < b < i as int + 1
                    implies bit_le(result[a] as int, result[b] as int) by {
                    if b < i as int {
                        assert(result[a] == before[a]);
                        assert(result[b] == before[b]);
                        assert(bit_le(before[a] as int, before[b] as int));
                    } else {
                        assert(result[a] == before[a]);
                        assert(result[i as int] == before[min_idx as int]);
                        assert(bit_le(before[a] as int, before[min_idx as int] as int));
                    }
                };
                assert forall|a: int, b: int| 0 <= a < i as int + 1 && i as int + 1 <= b < n as int
                    implies bit_le(result[a] as int, result[b] as int) by {
                    if a < i as int {
                        if b != min_idx as int {
                            assert(result[a] == before[a]);
                            assert(result[b] == before[b]);
                            assert(bit_le(before[a] as int, before[b] as int));
                        } else {
                            assert(result[a] == before[a]);
                            assert(result[min_idx as int] == before[i as int]);
                            assert(bit_le(before[a] as int, before[i as int] as int));
                        }
                    } else {
                        assert(result[i as int] == before[min_idx as int]);
                        if b != min_idx as int {
                            assert(result[b] == before[b]);
                            assert(bit_le(before[min_idx as int] as int, before[b] as int));
                        } else {
                            assert(result[min_idx as int] == before[i as int]);
                            assert(bit_le(before[min_idx as int] as int, before[i as int] as int));
                        }
                    }
                };
            }
            i = i + 1;
        }
        result
    }
}

}
