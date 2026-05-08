use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;





pub open spec fn can_jump_to(arr: Seq<i32>, d: int, from: int, to: int) -> bool {
    let lo = if from < to { from } else { to };
    let hi = if from < to { to } else { from };
    0 <= from < arr.len() as int
    && 0 <= to < arr.len() as int
    && from != to
    && hi - lo <= d
    && arr[from] > arr[to]
    && forall|k: int| lo < k < hi ==> arr[from] > arr[k]
}

pub open spec fn is_valid_path(arr: Seq<i32>, d: int, path: Seq<int>) -> bool {
    path.len() >= 1
    && (forall|i: int| 0 <= i < path.len() ==> 0 <= (#[trigger] path[i]) < arr.len())
    && (forall|i: int| 0 <= i < path.len() - 1 ==>
        can_jump_to(arr, d, (#[trigger] path[i]), path[i + 1]))
}

pub open spec fn has_path_of_length(arr: Seq<i32>, d: int, len: int) -> bool {
    exists|path: Seq<int>| path.len() == len && (#[trigger] is_valid_path(arr, d, path))
}





pub open spec fn right_dp(arr: Seq<i32>, d: int, i: int, j: int) -> nat
    decreases arr[i] as int, 1int, arr.len() as int - j
    when 0 <= i && i < arr.len() as int && 0 <= j
        && (forall|t: int| 0 <= t < arr.len() ==> (#[trigger] arr[t]) >= 1)
{
    if j >= arr.len() as int || j - i > d {
        0nat
    } else if arr[j] >= arr[i] {
        0nat
    } else {
        let cur = dp_at(arr, d, j);
        let rest = right_dp(arr, d, i, j + 1);
        if cur > rest { cur } else { rest }
    }
}

pub open spec fn left_dp(arr: Seq<i32>, d: int, i: int, j: int) -> nat
    decreases arr[i] as int, 1int, j + 1
    when 0 <= i && i < arr.len() as int && j < i
        && (forall|t: int| 0 <= t < arr.len() ==> (#[trigger] arr[t]) >= 1)
{
    if j < 0 || i - j > d {
        0nat
    } else if arr[j] >= arr[i] {
        0nat
    } else {
        let cur = dp_at(arr, d, j);
        let rest = left_dp(arr, d, i, j - 1);
        if cur > rest { cur } else { rest }
    }
}

pub open spec fn dp_at(arr: Seq<i32>, d: int, i: int) -> nat
    decreases arr[i] as int, 3int, 0int
    when 0 <= i && i < arr.len() as int
        && (forall|t: int| 0 <= t < arr.len() ==> (#[trigger] arr[t]) >= 1)
{
    let r = right_dp(arr, d, i, i + 1);
    let l = left_dp(arr, d, i, i - 1);
    1 + (if r >= l { r } else { l })
}

pub open spec fn max_dp_range(arr: Seq<i32>, d: int, end: int) -> nat
    decreases end,
{
    if end <= 0 {
        0nat
    } else {
        let prev = max_dp_range(arr, d, end - 1);
        let cur = dp_at(arr, d, end - 1);
        if cur > prev { cur } else { prev }
    }
}





pub open spec fn count_le(arr: Seq<i32>, val: int, end: int) -> nat
    decreases end,
{
    if end <= 0 {
        0nat
    } else {
        count_le(arr, val, end - 1) + if arr[end - 1] as int <= val { 1nat } else { 0nat }
    }
}





pub open spec fn is_perm(order: Seq<usize>, n: int) -> bool {
    order.len() == n
    && (forall|a: int| 0 <= a < n ==> 0 <= (#[trigger] order[a]) < n as usize)
    && (forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==>
        (#[trigger] order[a]) != (#[trigger] order[b]))
}

pub open spec fn appears_in(order: Seq<usize>, n: int, v: int) -> bool {
    exists|a: int| 0 <= a < n && (#[trigger] order[a]) == v as usize
}

pub open spec fn is_surjective(order: Seq<usize>, n: int) -> bool {
    forall|v: int| 0 <= v < n ==> (#[trigger] appears_in(order, n, v))
}

pub open spec fn sorted_by_arr(arr: Seq<i32>, order: Seq<usize>, end: int) -> bool {
    forall|a: int, b: int| 0 <= a < end && a < b < end ==>
        arr[(#[trigger] order[a]) as int] <= arr[(#[trigger] order[b]) as int]
}

pub open spec fn prefix_le_suffix(
    arr: Seq<i32>,
    order: Seq<usize>,
    boundary: int,
    n: int,
) -> bool {
    forall|a: int, b: int| 0 <= a < boundary && boundary <= b < n ==>
        arr[(#[trigger] order[a]) as int] <= arr[(#[trigger] order[b]) as int]
}





proof fn lemma_count_le_bound(arr: Seq<i32>, val: int, end: int)
    requires
        end >= 0,
        end <= arr.len(),
    ensures
        count_le(arr, val, end) <= end as nat,
    decreases end,
{
    if end > 0 {
        lemma_count_le_bound(arr, val, end - 1);
    }
}

proof fn lemma_count_le_mono_val(arr: Seq<i32>, val1: int, val2: int, end: int)
    requires
        val1 <= val2,
        end >= 0,
        end <= arr.len(),
    ensures
        count_le(arr, val1, end) <= count_le(arr, val2, end),
    decreases end,
{
    if end > 0 {
        lemma_count_le_mono_val(arr, val1, val2, end - 1);
    }
}

proof fn lemma_count_le_step(arr: Seq<i32>, val1: int, val2: int, end: int, w: int)
    requires
        0 <= w < end,
        end <= arr.len(),
        arr[w] as int > val1,
        arr[w] as int <= val2,
    ensures
        count_le(arr, val2, end) >= count_le(arr, val1, end) + 1,
    decreases end,
{
    if end == w + 1 {
        lemma_count_le_mono_val(arr, val1, val2, w);
    } else {
        lemma_count_le_step(arr, val1, val2, end - 1, w);
    }
}

proof fn lemma_right_dp_bound(arr: Seq<i32>, d: int, i: int, j: int)
    requires
        0 <= i < arr.len(),
        j >= i + 1,
        d >= 1,
        forall|t: int| 0 <= t < arr.len() ==> 1 <= (#[trigger] arr[t]) <= 100_000,
    ensures
        right_dp(arr, d, i, j) <= count_le(arr, arr[i] as int - 1, arr.len() as int),
    decreases arr[i] as int, 1int, arr.len() as int - j,
{
    if j >= arr.len() as int || j - i > d {
    } else if arr[j] >= arr[i] {
    } else {
        lemma_dp_at_le_count(arr, d, j);
        lemma_count_le_mono_val(arr, arr[j] as int, arr[i] as int - 1, arr.len() as int);
        lemma_right_dp_bound(arr, d, i, j + 1);
    }
}

proof fn lemma_left_dp_bound(arr: Seq<i32>, d: int, i: int, j: int)
    requires
        0 <= i < arr.len(),
        j <= i - 1,
        d >= 1,
        forall|t: int| 0 <= t < arr.len() ==> 1 <= (#[trigger] arr[t]) <= 100_000,
    ensures
        left_dp(arr, d, i, j) <= count_le(arr, arr[i] as int - 1, arr.len() as int),
    decreases arr[i] as int, 1int, j + 1,
{
    if j < 0 || i - j > d {
    } else if arr[j] >= arr[i] {
    } else {
        lemma_dp_at_le_count(arr, d, j);
        lemma_count_le_mono_val(arr, arr[j] as int, arr[i] as int - 1, arr.len() as int);
        lemma_left_dp_bound(arr, d, i, j - 1);
    }
}

proof fn lemma_dp_at_le_count(arr: Seq<i32>, d: int, i: int)
    requires
        0 <= i < arr.len(),
        d >= 1,
        forall|t: int| 0 <= t < arr.len() ==> 1 <= (#[trigger] arr[t]) <= 100_000,
    ensures
        dp_at(arr, d, i) <= count_le(arr, arr[i] as int, arr.len() as int),
    decreases arr[i] as int, 3int, 0int,
{
    lemma_right_dp_bound(arr, d, i, i + 1);
    lemma_left_dp_bound(arr, d, i, i - 1);
    lemma_count_le_step(arr, arr[i] as int - 1, arr[i] as int, arr.len() as int, i);
}

proof fn lemma_dp_at_bound(arr: Seq<i32>, d: int, i: int)
    requires
        0 <= i < arr.len(),
        arr.len() >= 1,
        d >= 1,
        forall|t: int| 0 <= t < arr.len() ==> 1 <= (#[trigger] arr[t]) <= 100_000,
    ensures
        1 <= dp_at(arr, d, i) <= arr.len() as nat,
{
    lemma_dp_at_le_count(arr, d, i);
    lemma_count_le_bound(arr, arr[i] as int, arr.len() as int);
}





proof fn lemma_right_dp_includes(arr: Seq<i32>, d: int, i: int, start: int, target: int)
    requires
        0 <= i < arr.len(),
        i < start,
        start <= target < arr.len() as int,
        can_jump_to(arr, d, i, target),
        forall|t: int| 0 <= t < arr.len() ==> 1 <= (#[trigger] arr[t]) <= 100_000,
    ensures
        right_dp(arr, d, i, start) >= dp_at(arr, d, target),
    decreases target - start,
{
    if start == target {
    } else {
        lemma_right_dp_includes(arr, d, i, start + 1, target);
    }
}

proof fn lemma_left_dp_includes(arr: Seq<i32>, d: int, i: int, start: int, target: int)
    requires
        0 <= i < arr.len(),
        start < i,
        0 <= target <= start,
        can_jump_to(arr, d, i, target),
        forall|t: int| 0 <= t < arr.len() ==> 1 <= (#[trigger] arr[t]) <= 100_000,
    ensures
        left_dp(arr, d, i, start) >= dp_at(arr, d, target),
    decreases start - target,
{
    if start == target {
    } else {
        lemma_left_dp_includes(arr, d, i, start - 1, target);
    }
}

proof fn lemma_right_dp_witness_helper(
    arr: Seq<i32>,
    d: int,
    i: int,
    j: int,
) -> (w: int)
    requires
        0 <= i < arr.len(),
        i < j,
        right_dp(arr, d, i, j) > 0,
        d >= 1,
        forall|t: int| 0 <= t < arr.len() ==> 1 <= (#[trigger] arr[t]) <= 100_000,
        forall|k: int| i < k < j ==> arr[i] > arr[k],
    ensures
        j <= w < arr.len() as int,
        can_jump_to(arr, d, i, w),
        dp_at(arr, d, w) == right_dp(arr, d, i, j),
    decreases arr.len() as int - j,
{
    let cur = dp_at(arr, d, j);
    let rest = right_dp(arr, d, i, j + 1);
    if cur >= rest {
        j
    } else {
        lemma_right_dp_witness_helper(arr, d, i, j + 1)
    }
}

proof fn lemma_left_dp_witness_helper(
    arr: Seq<i32>,
    d: int,
    i: int,
    j: int,
) -> (w: int)
    requires
        0 <= i < arr.len(),
        0 <= j < i,
        left_dp(arr, d, i, j) > 0,
        d >= 1,
        forall|t: int| 0 <= t < arr.len() ==> 1 <= (#[trigger] arr[t]) <= 100_000,
        forall|k: int| j < k < i ==> arr[i] > arr[k],
    ensures
        0 <= w <= j,
        w < arr.len() as int,
        can_jump_to(arr, d, i, w),
        dp_at(arr, d, w) == left_dp(arr, d, i, j),
    decreases j + 1,
{
    let cur = dp_at(arr, d, j);
    let rest = left_dp(arr, d, i, j - 1);
    if cur >= rest {
        j
    } else {
        lemma_left_dp_witness_helper(arr, d, i, j - 1)
    }
}

proof fn lemma_prepend_valid_path(
    arr: Seq<i32>,
    d: int,
    i: int,
    w: int,
    sub: Seq<int>,
)
    requires
        0 <= i < arr.len() as int,
        0 <= w < arr.len() as int,
        can_jump_to(arr, d, i, w),
        is_valid_path(arr, d, sub),
        sub[0] == w,
    ensures
        is_valid_path(arr, d, seq![i].add(sub)),
{
    let path = seq![i].add(sub);
    assert(path.len() >= 1);
    assert forall|ii: int| 0 <= ii < path.len() implies
        0 <= (#[trigger] path[ii]) < arr.len()
    by {
        if ii == 0 {
            assert(path[0] == i);
        } else {
            assert(path[ii] == sub[ii - 1]);
        }
    }
    assert forall|ii: int| 0 <= ii < path.len() - 1 implies
        can_jump_to(arr, d, (#[trigger] path[ii]), path[ii + 1])
    by {
        if ii == 0 {
            assert(path[0] == i);
            assert(path[1] == sub[0]);
        } else {
            assert(path[ii] == sub[ii - 1]);
            assert(path[ii + 1] == sub[ii]);
        }
    }
}

proof fn lemma_has_path_from(arr: Seq<i32>, d: int, i: int) -> (path: Seq<int>)
    requires
        0 <= i < arr.len(),
        d >= 1,
        forall|t: int| 0 <= t < arr.len() ==> 1 <= (#[trigger] arr[t]) <= 100_000,
    ensures
        path.len() == dp_at(arr, d, i) as int,
        is_valid_path(arr, d, path),
        path[0] == i,
    decreases arr[i] as int,
{
    let r = right_dp(arr, d, i, i + 1);
    let l = left_dp(arr, d, i, i - 1);
    let best = if r >= l { r } else { l };
    if best == 0nat {
        let path: Seq<int> = seq![i];
        assert(is_valid_path(arr, d, path)) by {
            assert(path.len() >= 1);
            assert forall|ii: int| 0 <= ii < path.len() implies
                0 <= (#[trigger] path[ii]) < arr.len()
            by { assert(path[0] == i); }
        }
        path
    } else if r >= l {
        let w = lemma_right_dp_witness_helper(arr, d, i, i + 1);
        let sub = lemma_has_path_from(arr, d, w);
        let path: Seq<int> = seq![i].add(sub);
        lemma_prepend_valid_path(arr, d, i, w, sub);
        path
    } else {
        let w = lemma_left_dp_witness_helper(arr, d, i, i - 1);
        let sub = lemma_has_path_from(arr, d, w);
        let path: Seq<int> = seq![i].add(sub);
        lemma_prepend_valid_path(arr, d, i, w, sub);
        path
    }
}

proof fn lemma_path_le_dp(arr: Seq<i32>, d: int, path: Seq<int>)
    requires
        is_valid_path(arr, d, path),
        d >= 1,
        forall|t: int| 0 <= t < arr.len() ==> 1 <= (#[trigger] arr[t]) <= 100_000,
    ensures
        path.len() <= dp_at(arr, d, path[0]) as int,
    decreases path.len(),
{
    if path.len() <= 1 {
    } else {
        let i = path[0];
        let j = path[1];
        let sub = path.subrange(1, path.len() as int);
        assert(sub.len() >= 1);
        assert forall|ii: int| 0 <= ii < sub.len() implies
            0 <= (#[trigger] sub[ii]) < arr.len()
        by { assert(sub[ii] == path[ii + 1]); }
        assert forall|ii: int| 0 <= ii < sub.len() - 1 implies
            can_jump_to(arr, d, (#[trigger] sub[ii]), sub[ii + 1])
        by {
            assert(sub[ii] == path[ii + 1]);
            assert(sub[ii + 1] == path[ii + 2]);
        }
        assert(is_valid_path(arr, d, sub));
        lemma_path_le_dp(arr, d, sub);
        assert(can_jump_to(arr, d, i, j));
        if j > i {
            lemma_right_dp_includes(arr, d, i, i + 1, j);
        } else {
            lemma_left_dp_includes(arr, d, i, i - 1, j);
        }
    }
}

proof fn lemma_max_dp_range_includes(arr: Seq<i32>, d: int, end: int, i: int)
    requires
        0 <= i < end,
        end <= arr.len(),
    ensures
        max_dp_range(arr, d, end) >= dp_at(arr, d, i),
    decreases end,
{
    if i == end - 1 {
    } else {
        lemma_max_dp_range_includes(arr, d, end - 1, i);
    }
}

proof fn lemma_max_dp_achievable(arr: Seq<i32>, d: int, n: int)
    requires
        1 <= n <= arr.len(),
        d >= 1,
        forall|t: int| 0 <= t < arr.len() ==> 1 <= (#[trigger] arr[t]) <= 100_000,
    ensures
        has_path_of_length(arr, d, max_dp_range(arr, d, n) as int),
    decreases n,
{
    let cur = dp_at(arr, d, n - 1);
    lemma_dp_at_bound(arr, d, n - 1);
    if n == 1 {
        assert(max_dp_range(arr, d, 0) == 0nat);
        assert(cur >= 1);
        assert(max_dp_range(arr, d, 1) == cur);
        let _ = lemma_has_path_from(arr, d, 0);
    } else {
        let prev = max_dp_range(arr, d, n - 1);
        if cur > prev {
            let _ = lemma_has_path_from(arr, d, n - 1);
        } else {
            lemma_max_dp_achievable(arr, d, n - 1);
        }
    }
}

proof fn lemma_max_dp_range_bound(arr: Seq<i32>, d: int, n: int)
    requires
        1 <= n <= arr.len(),
        d >= 1,
        forall|t: int| 0 <= t < arr.len() ==> 1 <= (#[trigger] arr[t]) <= 100_000,
    ensures
        1 <= max_dp_range(arr, d, n) <= arr.len() as nat,
    decreases n,
{
    lemma_dp_at_bound(arr, d, n - 1);
    if n > 1 {
        lemma_max_dp_range_bound(arr, d, n - 1);
    }
}

proof fn lemma_no_longer_path(arr: Seq<i32>, d: int, k: int)
    requires
        arr.len() >= 1,
        d >= 1,
        forall|t: int| 0 <= t < arr.len() ==> 1 <= (#[trigger] arr[t]) <= 100_000,
        k > max_dp_range(arr, d, arr.len() as int) as int,
    ensures
        !has_path_of_length(arr, d, k),
{
    if has_path_of_length(arr, d, k) {
        let path = choose|path: Seq<int>|
            path.len() == k && (#[trigger] is_valid_path(arr, d, path));
        let start = path[0];
        lemma_path_le_dp(arr, d, path);
        lemma_max_dp_range_includes(arr, d, arr.len() as int, start);
    }
}





proof fn lemma_swap_perm(order: Seq<usize>, i: int, j: int, n: int)
    requires
        is_perm(order, n),
        0 <= i < n,
        0 <= j < n,
    ensures
        is_perm(order.update(i, order[j]).update(j, order[i]), n),
{
    let nw = order.update(i, order[j]).update(j, order[i]);
    assert(nw.len() == n);
    assert forall|a: int| 0 <= a < n implies
        0 <= (#[trigger] nw[a]) < n as usize
    by {
        if a == j { assert(nw[a] == order[i]); }
        else if a == i && i != j { assert(nw[a] == order[j]); }
        else { assert(nw[a] == order[a]); }
    }
    assert forall|a: int, b: int|
        0 <= a < n && 0 <= b < n && a != b
        implies (#[trigger] nw[a]) != (#[trigger] nw[b])
    by {
        if a == i && b == j { }
        else if a == j && b == i { }
        else if a == i && i != j {
            assert(nw[a] == order[j]);
            if b == j { assert(nw[b] == order[i]); }
            else { assert(nw[b] == order[b]); }
        } else if a == j {
            assert(nw[a] == order[i]);
            if b == i && i != j { assert(nw[b] == order[j]); }
            else { assert(nw[b] == order[b]); }
        } else if b == i && i != j {
            assert(nw[a] == order[a]);
            assert(nw[b] == order[j]);
        } else if b == j {
            assert(nw[a] == order[a]);
            assert(nw[b] == order[i]);
        } else {
            assert(nw[a] == order[a]);
            assert(nw[b] == order[b]);
        }
    }
}

proof fn lemma_swap_surj(order: Seq<usize>, i: int, j: int, n: int)
    requires
        is_surjective(order, n),
        order.len() == n,
        0 <= i < n,
        0 <= j < n,
    ensures
        is_surjective(order.update(i, order[j]).update(j, order[i]), n),
{
    let nw = order.update(i, order[j]).update(j, order[i]);
    let mid = order.update(i, order[j]);
    assert(mid.len() == n);
    assert(nw.len() == n);
    assert forall|v: int| 0 <= v < n implies
        (#[trigger] appears_in(nw, n, v))
    by {
        assert(appears_in(order, n, v));
        let a0 = choose|a: int| 0 <= a < n && (#[trigger] order[a]) == v as usize;
        if a0 == i {
            if i == j {
                
                
                assert(nw[a0] == order[i]);
            } else {
                
                assert(0 <= j < nw.len() as int);
                assert(nw[j] == order[i]);
            }
        } else if a0 == j {
            if i == j {
                assert(nw[a0] == order[i]);
            } else {
                
                assert(0 <= i < mid.len() as int);
                assert(mid[i] == order[j]);
                assert(nw[i] == mid[i]);
            }
        } else {
            
            assert(mid[a0] == order[a0]);
            assert(nw[a0] == mid[a0]);
        }
    }
}





pub open spec fn left_scan_best(arr: Seq<i32>, d: int, i: int, j: int, best: nat) -> nat
    decreases j + 1
    when 0 <= i && i < arr.len() as int
        && (forall|t: int| 0 <= t < arr.len() ==> (#[trigger] arr[t]) >= 1)
{
    if j < 0 || i - j > d { best }
    else if arr[j] >= arr[i] { best }
    else {
        let new_best = if dp_at(arr, d, j) > best { dp_at(arr, d, j) } else { best };
        left_scan_best(arr, d, i, j - 1, new_best)
    }
}

proof fn lemma_left_scan_correct(arr: Seq<i32>, d: int, i: int, j: int, best: nat)
    requires
        0 <= i < arr.len(),
        j < i,
        d >= 1,
        forall|t: int| 0 <= t < arr.len() ==> 1 <= (#[trigger] arr[t]) <= 100_000,
    ensures
        left_scan_best(arr, d, i, j, best) ==
            (if best >= left_dp(arr, d, i, j) { best } else { left_dp(arr, d, i, j) }),
    decreases j + 1,
{
    if j < 0 || i - j > d {
    } else if arr[j] >= arr[i] {
    } else {
        let new_best = if dp_at(arr, d, j) > best { dp_at(arr, d, j) } else { best };
        lemma_left_scan_correct(arr, d, i, j - 1, new_best);
    }
}





impl Solution {
    pub fn max_jumps(arr: Vec<i32>, d: i32) -> (result: i32)
        requires
            1 <= arr.len() <= 1000,
            1 <= d <= arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> 1 <= (#[trigger] arr[i]) <= 100_000,
        ensures
            1 <= result <= arr@.len() as i32,
            has_path_of_length(arr@, d as int, result as int),
            forall|k: int| k > result as int ==> !has_path_of_length(arr@, d as int, k),
    {
        let n = arr.len();
        let du = d as usize;

        
        let mut order: Vec<usize> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                n == arr.len(),
                n <= 1000,
                0 <= i <= n,
                order.len() == i,
                forall|a: int| 0 <= a < i ==> (#[trigger] order[a]) == a as usize,
            decreases n - i,
        {
            order.push(i);
            i += 1;
        }

        proof {
            assert(is_perm(order@, n as int)) by {
                assert(order@.len() == n as int);
                assert forall|a: int| 0 <= a < n as int implies
                    0 <= (#[trigger] order@[a]) < n as usize
                by { assert(order@[a] == a as usize); }
                assert forall|a: int, b: int|
                    0 <= a < n as int && 0 <= b < n as int && a != b
                    implies (#[trigger] order@[a]) != (#[trigger] order@[b])
                by {
                    assert(order@[a] == a as usize);
                    assert(order@[b] == b as usize);
                }
            }
            assert(is_surjective(order@, n as int)) by {
                assert forall|v: int| 0 <= v < n as int implies
                    (#[trigger] appears_in(order@, n as int, v))
                by {
                    assert(order@[v] == v as usize);
                }
            }
            assert(sorted_by_arr(arr@, order@, 0));
            assert(prefix_le_suffix(arr@, order@, 0, n as int));
        }

        
        i = 0;
        while i < n
            invariant
                n == arr.len(),
                n <= 1000,
                du == d as usize,
                du <= n,
                0 <= i <= n,
                order.len() == n,
                is_perm(order@, n as int),
                is_surjective(order@, n as int),
                sorted_by_arr(arr@, order@, i as int),
                prefix_le_suffix(arr@, order@, i as int, n as int),
                forall|ii: int| 0 <= ii < arr.len() ==> 1 <= (#[trigger] arr[ii]) <= 100_000,
            decreases n - i,
        {
            let mut min_k = i;
            let mut j = i + 1;
            while j < n
                invariant
                    n == arr.len(),
                    n <= 1000,
                    0 <= i < n,
                    i < j <= n,
                    i <= min_k < j,
                    order.len() == n,
                    is_perm(order@, n as int),
                    is_surjective(order@, n as int),
                    sorted_by_arr(arr@, order@, i as int),
                    prefix_le_suffix(arr@, order@, i as int, n as int),
                    forall|t: int| i as int <= t < j as int ==>
                        arr@[order@[min_k as int] as int] <= arr@[order@[t] as int],
                    forall|ii: int| 0 <= ii < arr.len() ==> 1 <= (#[trigger] arr[ii]) <= 100_000,
                decreases n - j,
            {
                if arr[order[j]] < arr[order[min_k]] {
                    min_k = j;
                }
                j += 1;
            }

            let ghost old_order = order@;
            let tmp = order[i];
            order.set(i, order[min_k]);
            order.set(min_k, tmp);

            proof {
                
                let nw = old_order.update(i as int, old_order[min_k as int]).update(
                    min_k as int,
                    old_order[i as int],
                );
                
                assert(order@ =~= nw);
                lemma_swap_perm(old_order, i as int, min_k as int, n as int);
                lemma_swap_surj(old_order, i as int, min_k as int, n as int);

                
                assert forall|a: int, b: int|
                    0 <= a < (i + 1) as int && a < b < (i + 1) as int
                    implies arr@[(#[trigger] order@[a]) as int] <= arr@[(#[trigger] order@[b]) as int]
                by {
                    if b < i as int {
                        assert(order@[a] == old_order[a]);
                        assert(order@[b] == old_order[b]);
                    } else {
                        
                        assert(order@[a] == old_order[a]);
                        assert(order@[i as int] == old_order[min_k as int]);
                    }
                }

                
                assert forall|a: int, b: int|
                    0 <= a < (i + 1) as int && (i + 1) as int <= b < n as int
                    implies arr@[(#[trigger] order@[a]) as int] <= arr@[(#[trigger] order@[b]) as int]
                by {
                    if b as usize == min_k {
                        assert(order@[b] == old_order[i as int]);
                        if a < i as int {
                            assert(order@[a] == old_order[a]);
                        } else {
                            assert(order@[a] == old_order[min_k as int]);
                        }
                    } else {
                        assert(order@[b] == old_order[b]);
                        if a < i as int {
                            assert(order@[a] == old_order[a]);
                        } else {
                            assert(order@[a] == old_order[min_k as int]);
                        }
                    }
                }
            }

            i += 1;
        }

        
        let mut dp: Vec<i32> = Vec::new();
        i = 0;
        while i < n
            invariant
                n == arr.len(),
                n <= 1000,
                0 <= i <= n,
                dp.len() == i,
                forall|j: int| 0 <= j < i ==> (#[trigger] dp[j]) == 1i32,
            decreases n - i,
        {
            dp.push(1i32);
            i += 1;
        }

        
        let mut k: usize = 0;
        while k < n
            invariant
                n == arr.len(),
                n <= 1000,
                du == d as usize,
                du <= n,
                d >= 1,
                0 <= k <= n,
                dp.len() == n,
                order.len() == n,
                is_perm(order@, n as int),
                is_surjective(order@, n as int),
                sorted_by_arr(arr@, order@, n as int),
                forall|ii: int| 0 <= ii < arr.len() ==> 1 <= (#[trigger] arr[ii]) <= 100_000,
                forall|kk: int| 0 <= kk < k ==>
                    (#[trigger] dp[order@[kk] as int]) as nat
                        == dp_at(arr@, d as int, order@[kk] as int),
                forall|kk: int| 0 <= kk < k ==>
                    1 <= (#[trigger] dp[order@[kk] as int]) <= n as i32,
                forall|kk: int| k <= kk < n ==>
                    (#[trigger] dp[order@[kk] as int]) == 1i32,
            decreases n - k,
        {
            let idx = order[k];

            
            
            

            let mut best: i32 = 0;
            let ghost right_total: nat = right_dp(arr@, d as int, idx as int, idx as int + 1);

            
            let mut j = idx + 1;
            while j < n && j <= idx + du
                invariant
                    n == arr.len(),
                    n <= 1000,
                    du == d as usize,
                    du <= n,
                    d >= 1,
                    0 <= k < n,
                    0 <= idx < n,
                    idx == order[k as int],
                    idx as int + 1 <= j as int,
                    j <= n,
                    j as int <= idx as int + du as int + 1,
                    dp.len() == n,
                    best >= 0,
                    best as nat <= right_total,
                    right_total == (
                        if best as nat >= right_dp(arr@, d as int, idx as int, j as int) {
                            best as nat
                        } else {
                            right_dp(arr@, d as int, idx as int, j as int)
                        }
                    ),
                    forall|t: int| idx as int + 1 <= t < j as int ==>
                        arr[t] < arr[idx as int],
                    order.len() == n,
                    is_perm(order@, n as int),
                    is_surjective(order@, n as int),
                    sorted_by_arr(arr@, order@, n as int),
                    forall|ii: int| 0 <= ii < arr.len() ==> 1 <= (#[trigger] arr[ii]) <= 100_000,
                    forall|kk: int| 0 <= kk < k ==>
                        (#[trigger] dp[order@[kk] as int]) as nat
                            == dp_at(arr@, d as int, order@[kk] as int),
                    forall|kk: int| 0 <= kk < k ==>
                        1 <= (#[trigger] dp[order@[kk] as int]) <= n as i32,
                    forall|kk: int| k <= kk < n ==>
                        (#[trigger] dp[order@[kk] as int]) == 1i32,
                ensures
                    right_dp(arr@, d as int, idx as int, j as int) == 0nat,
                    best as nat == right_total,
                    best >= 0,
                    dp.len() == n,
                    forall|kk: int| 0 <= kk < k ==>
                        (#[trigger] dp[order@[kk] as int]) as nat
                            == dp_at(arr@, d as int, order@[kk] as int),
                    forall|kk: int| 0 <= kk < k ==>
                        1 <= (#[trigger] dp[order@[kk] as int]) <= n as i32,
                    forall|kk: int| k <= kk < n ==>
                        (#[trigger] dp[order@[kk] as int]) == 1i32,
                decreases n - j,
            {
                if arr[j] >= arr[idx] {
                    break;
                }
                
                proof {
                    assert(appears_in(order@, n as int, j as int));
                    let jj = choose|a: int|
                        0 <= a < n as int && (#[trigger] order@[a]) == j as usize;
                    assert(arr@[order@[jj] as int] < arr@[order@[k as int] as int]);
                    if jj >= k as int {
                    }
                    assert(jj < k as int);
                    assert(dp[j as int] as nat == dp_at(arr@, d as int, j as int));
                }
                if dp[j] > best {
                    best = dp[j];
                }
                j += 1;
            }

            
            let left_bound: usize = if idx >= du { idx - du } else { 0 };
            let ghost left_target: nat =
                if right_total >= left_dp(arr@, d as int, idx as int, idx as int - 1) {
                    right_total
                } else {
                    left_dp(arr@, d as int, idx as int, idx as int - 1)
                };
            j = idx;
            while j > left_bound
                invariant
                    n == arr.len(),
                    n <= 1000,
                    du == d as usize,
                    du <= n,
                    d >= 1,
                    0 <= k < n,
                    0 <= idx < n,
                    idx == order[k as int],
                    left_bound <= j <= idx,
                    left_bound == (if idx >= du { (idx - du) as int } else { 0int }) as usize,
                    dp.len() == n,
                    best >= 0,
                    best as nat >= right_total,
                    (j as int) < (idx as int) ==> arr@[j as int] < arr@[idx as int],
                    forall|t: int| j as int <= t && t < idx as int
                        && arr@[t] < arr@[idx as int]
                        ==> best as nat >= dp_at(arr@, d as int, t),
                    (j as int == idx as int) ==>
                        (if best as nat >= left_dp(arr@, d as int, idx as int, idx as int - 1)
                         { best as nat } else { left_dp(arr@, d as int, idx as int, idx as int - 1) })
                            == left_target,
                    (j as int) < (idx as int) ==>
                        (if best as nat >= left_dp(arr@, d as int, idx as int, j as int)
                         { best as nat } else { left_dp(arr@, d as int, idx as int, j as int) })
                            == left_target,
                    order.len() == n,
                    is_perm(order@, n as int),
                    is_surjective(order@, n as int),
                    sorted_by_arr(arr@, order@, n as int),
                    forall|ii: int| 0 <= ii < arr.len() ==> 1 <= (#[trigger] arr[ii]) <= 100_000,
                    forall|kk: int| 0 <= kk < k ==>
                        (#[trigger] dp[order@[kk] as int]) as nat
                            == dp_at(arr@, d as int, order@[kk] as int),
                    forall|kk: int| 0 <= kk < k ==>
                        1 <= (#[trigger] dp[order@[kk] as int]) <= n as i32,
                    forall|kk: int| k <= kk < n ==>
                        (#[trigger] dp[order@[kk] as int]) == 1i32,
                    ((j as int) == (left_bound as int) && (j as int) < (idx as int)) ==>
                        best as nat >= left_dp(arr@, d as int, idx as int, j as int),
                ensures
                    best as nat == left_target,
                    dp.len() == n,
                    best >= 0,
                    forall|kk: int| 0 <= kk < k ==>
                        (#[trigger] dp[order@[kk] as int]) as nat
                            == dp_at(arr@, d as int, order@[kk] as int),
                    forall|kk: int| 0 <= kk < k ==>
                        1 <= (#[trigger] dp[order@[kk] as int]) <= n as i32,
                    forall|kk: int| k <= kk < n ==>
                        (#[trigger] dp[order@[kk] as int]) == 1i32,
                decreases j - left_bound,
            {
                j -= 1;
                if arr[j] >= arr[idx] {
                    proof {
                        
                        assert(left_dp(arr@, d as int, idx as int, j as int) == 0nat);
                        if (j as int + 1) < (idx as int) {
                            
                            
                            assert(left_dp(arr@, d as int, idx as int, (j + 1) as int)
                                == dp_at(arr@, d as int, (j + 1) as int));
                            assert(best as nat >= dp_at(arr@, d as int, (j + 1) as int));
                        }
                    }
                    j += 1;
                    break;
                }
                proof {
                    assert(appears_in(order@, n as int, j as int));
                    let jj = choose|a: int|
                        0 <= a < n as int && (#[trigger] order@[a]) == j as usize;
                    assert(arr@[order@[jj] as int] < arr@[order@[k as int] as int]);
                    if jj >= k as int { }
                    assert(jj < k as int);
                    assert(dp[j as int] as nat == dp_at(arr@, d as int, j as int));
                }
                if dp[j] > best {
                    best = dp[j];
                }
                proof {
                    if (j + 1) as int == idx as int {
                    } else {
                        assert(arr@[(j + 1) as int] < arr@[idx as int]);
                        assert(best as nat >= dp_at(arr@, d as int, (j + 1) as int));
                    }
                }
                proof {
                    if (j as int) == (left_bound as int) && (j as int) < (idx as int) {
                        assert(left_dp(arr@, d as int, idx as int, j as int - 1) == 0nat);
                        assert(left_dp(arr@, d as int, idx as int, j as int)
                            == dp_at(arr@, d as int, j as int));
                        assert(best as nat >= dp_at(arr@, d as int, j as int));
                    }
                }
            }
            
            proof {
                lemma_dp_at_bound(arr@, d as int, idx as int);
                assert(1 <= best + 1 <= n as i32);
            }
            dp.set(idx, best + 1);
            k += 1;
        }

        
        proof {
            assert forall|j: int| 0 <= j < n as int implies
                (#[trigger] dp[j]) as nat == dp_at(arr@, d as int, j)
            by {
                assert(appears_in(order@, n as int, j));
                let kk = choose|a: int|
                    0 <= a < n as int && (#[trigger] order@[a]) == j as usize;
                assert(dp[order@[kk] as int] as nat == dp_at(arr@, d as int, order@[kk] as int));
            }
            assert forall|j: int| 0 <= j < n as int implies
                1 <= (#[trigger] dp[j]) <= n as i32
            by {
                assert(appears_in(order@, n as int, j));
                let kk = choose|a: int|
                    0 <= a < n as int && (#[trigger] order@[a]) == j as usize;
                assert(1 <= dp[order@[kk] as int] <= n as i32);
            }
        }

        
        let mut best_val = dp[0];
        proof {
            
            
            
            lemma_dp_at_bound(arr@, d as int, 0);
            assert(max_dp_range(arr@, d as int, 0) == 0nat);
            assert(dp[0] as nat == dp_at(arr@, d as int, 0));
        }
        i = 1;
        while i < n
            invariant
                n == arr.len(),
                n <= 1000,
                dp.len() == n,
                1 <= i <= n,
                best_val as nat == max_dp_range(arr@, d as int, i as int),
                1 <= best_val <= n as i32,
                forall|j: int| 0 <= j < n as int ==>
                    (#[trigger] dp[j]) as nat == dp_at(arr@, d as int, j),
                forall|j: int| 0 <= j < n as int ==> 1 <= (#[trigger] dp[j]) <= n as i32,
                forall|ii: int| 0 <= ii < arr.len() ==> 1 <= (#[trigger] arr[ii]) <= 100_000,
                d >= 1,
            decreases n - i,
        {
            if dp[i] > best_val {
                best_val = dp[i];
            }
            i += 1;
        }

        proof {
            lemma_max_dp_achievable(arr@, d as int, n as int);
            lemma_max_dp_range_bound(arr@, d as int, n as int);
            assert forall|kk: int| kk > best_val as int implies
                !has_path_of_length(arr@, d as int, kk)
            by {
                lemma_no_longer_path(arr@, d as int, kk);
            }
        }

        best_val
    }
}

}
