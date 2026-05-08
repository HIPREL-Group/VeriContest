use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn non_decreasing(seq: Seq<i64>, lo: int, hi: int) -> bool
    recommends lo <= hi,
{
    forall|i: int| lo <= i && i < hi ==> #[trigger] seq[i] <= seq[i + 1]
}

pub open spec fn non_increasing(seq: Seq<i64>, lo: int, hi: int) -> bool
    recommends lo <= hi,
{
    forall|i: int| lo <= i && i < hi ==> #[trigger] seq[i] >= seq[i + 1]
}

pub open spec fn is_ladder(seq: Seq<i64>, l: int, r: int) -> bool
    recommends 0 <= l && l <= r && r < seq.len(),
{
    exists|k: int|
        l <= k && k <= r && non_decreasing(seq, l, k) && non_increasing(seq, k, r)
}

pub open spec fn up_end_spec(seq: Seq<i64>, i: int) -> int
    recommends 0 <= i && i < seq.len(),
    decreases (seq.len() - 1 - i) as nat,
{
    if i + 1 >= seq.len() {
        i
    } else if seq[i] <= seq[i + 1] {
        up_end_spec(seq, i + 1)
    } else {
        i
    }
}

pub open spec fn down_end_spec(seq: Seq<i64>, i: int) -> int
    recommends 0 <= i && i < seq.len(),
    decreases (seq.len() - 1 - i) as nat,
{
    if i + 1 >= seq.len() {
        i
    } else if seq[i] >= seq[i + 1] {
        down_end_spec(seq, i + 1)
    } else {
        i
    }
}

pub open spec fn ladder_end_spec(seq: Seq<i64>, l: int) -> int
    recommends 0 <= l && l < seq.len(),
{
    down_end_spec(seq, up_end_spec(seq, l))
}

proof fn lemma_non_decreasing_prefix(seq: Seq<i64>, lo: int, hi: int, end: int)
    requires
        0 <= lo <= hi <= end < seq.len(),
        non_decreasing(seq, lo, end),
    ensures
        non_decreasing(seq, lo, hi),
{
    assert forall|i: int| lo <= i && i < hi implies #[trigger] seq[i] <= seq[i + 1] by {
    }
}

proof fn lemma_non_decreasing_suffix(seq: Seq<i64>, lo: int, mid: int, hi: int)
    requires
        0 <= lo <= mid <= hi < seq.len(),
        non_decreasing(seq, lo, hi),
    ensures
        non_decreasing(seq, mid, hi),
{
    assert forall|i: int| mid <= i && i < hi implies #[trigger] seq[i] <= seq[i + 1] by {
    }
}

proof fn lemma_non_increasing_prefix(seq: Seq<i64>, lo: int, hi: int, end: int)
    requires
        0 <= lo <= hi <= end < seq.len(),
        non_increasing(seq, lo, end),
    ensures
        non_increasing(seq, lo, hi),
{
    assert forall|i: int| lo <= i && i < hi implies #[trigger] seq[i] >= seq[i + 1] by {
    }
}

proof fn lemma_non_increasing_suffix(seq: Seq<i64>, lo: int, mid: int, hi: int)
    requires
        0 <= lo <= mid <= hi < seq.len(),
        non_increasing(seq, lo, hi),
    ensures
        non_increasing(seq, mid, hi),
{
    assert forall|i: int| mid <= i && i < hi implies #[trigger] seq[i] >= seq[i + 1] by {
    }
}

proof fn lemma_up_end_bounds(seq: Seq<i64>, i: int)
    requires
        0 <= i && i < seq.len(),
    ensures
        i <= up_end_spec(seq, i) && up_end_spec(seq, i) < seq.len(),
    decreases (seq.len() - 1 - i) as nat,
{
    if i + 1 < seq.len() && seq[i] <= seq[i + 1] {
        lemma_up_end_bounds(seq, i + 1);
    }
}

proof fn lemma_down_end_bounds(seq: Seq<i64>, i: int)
    requires
        0 <= i && i < seq.len(),
    ensures
        i <= down_end_spec(seq, i) && down_end_spec(seq, i) < seq.len(),
    decreases (seq.len() - 1 - i) as nat,
{
    if i + 1 < seq.len() && seq[i] >= seq[i + 1] {
        lemma_down_end_bounds(seq, i + 1);
    }
}

proof fn lemma_up_end_is_non_decreasing(seq: Seq<i64>, i: int)
    requires
        0 <= i && i < seq.len(),
    ensures
        non_decreasing(seq, i, up_end_spec(seq, i)),
    decreases (seq.len() - 1 - i) as nat,
{
    if i + 1 < seq.len() && seq[i] <= seq[i + 1] {
        lemma_up_end_is_non_decreasing(seq, i + 1);
        assert forall|j: int| i <= j && j < up_end_spec(seq, i) implies #[trigger] seq[j] <= seq[j + 1] by {
            if j == i {
            } else {
                assert(i + 1 <= j && j < up_end_spec(seq, i + 1));
            }
        }
    }
}

proof fn lemma_down_end_is_non_increasing(seq: Seq<i64>, i: int)
    requires
        0 <= i && i < seq.len(),
    ensures
        non_increasing(seq, i, down_end_spec(seq, i)),
    decreases (seq.len() - 1 - i) as nat,
{
    if i + 1 < seq.len() && seq[i] >= seq[i + 1] {
        lemma_down_end_is_non_increasing(seq, i + 1);
        assert forall|j: int| i <= j && j < down_end_spec(seq, i) implies #[trigger] seq[j] >= seq[j + 1] by {
            if j == i {
            } else {
                assert(i + 1 <= j && j < down_end_spec(seq, i + 1));
            }
        }
    }
}

proof fn lemma_up_end_maximal(seq: Seq<i64>, i: int, j: int)
    requires
        0 <= i <= j < seq.len(),
        non_decreasing(seq, i, j),
    ensures
        j <= up_end_spec(seq, i),
    decreases j - i,
{
    if j == i {
        lemma_up_end_bounds(seq, i);
    } else {
        assert(seq[i] <= seq[i + 1]);
        lemma_non_decreasing_suffix(seq, i, i + 1, j);
        lemma_up_end_maximal(seq, i + 1, j);
        reveal_with_fuel(up_end_spec, 2);
        assert(up_end_spec(seq, i) == up_end_spec(seq, i + 1));
        assert(j <= up_end_spec(seq, i + 1));
        assert(j <= up_end_spec(seq, i));
    }
}

proof fn lemma_down_end_maximal(seq: Seq<i64>, i: int, j: int)
    requires
        0 <= i <= j < seq.len(),
        non_increasing(seq, i, j),
    ensures
        j <= down_end_spec(seq, i),
    decreases j - i,
{
    if j == i {
        lemma_down_end_bounds(seq, i);
    } else {
        assert(seq[i] >= seq[i + 1]);
        lemma_non_increasing_suffix(seq, i, i + 1, j);
        lemma_down_end_maximal(seq, i + 1, j);
        reveal_with_fuel(down_end_spec, 2);
        assert(down_end_spec(seq, i) == down_end_spec(seq, i + 1));
        assert(j <= down_end_spec(seq, i + 1));
        assert(j <= down_end_spec(seq, i));
    }
}

proof fn lemma_is_ladder_iff_bound(seq: Seq<i64>, l: int, r: int)
    requires
        0 <= l && l <= r && r < seq.len(),
    ensures
        is_ladder(seq, l, r) == (r <= ladder_end_spec(seq, l)),
{
    let p = up_end_spec(seq, l);
    lemma_up_end_bounds(seq, l);
    lemma_down_end_bounds(seq, p);
    if is_ladder(seq, l, r) {
        let k = choose|k: int|
            l <= k && k <= r && non_decreasing(seq, l, k) && non_increasing(seq, k, r);
        lemma_up_end_maximal(seq, l, k);
        if p < r {
            lemma_non_increasing_suffix(seq, k, p, r);
            lemma_down_end_maximal(seq, p, r);
        }
    } else {
        if r <= ladder_end_spec(seq, l) {
            lemma_up_end_is_non_decreasing(seq, l);
            if p <= r {
                lemma_down_end_is_non_increasing(seq, p);
                lemma_non_increasing_prefix(seq, p, r, ladder_end_spec(seq, l));
                assert(is_ladder(seq, l, r)) by {
                    assert(non_decreasing(seq, l, p));
                    assert(non_increasing(seq, p, r));
                }
            } else {
                lemma_non_decreasing_prefix(seq, l, r, p);
                assert(is_ladder(seq, l, r)) by {
                    assert(non_decreasing(seq, l, r));
                    assert(non_increasing(seq, r, r));
                }
            }
            assert(false);
        }
    }
}

impl Solution {
    pub fn query_ladders(arr: Vec<i64>, queries: Vec<(i32, i32)>) -> (res: Vec<bool>)
        requires
            1 <= arr.len() <= 100_000,
            1 <= queries.len() <= 100_000,
            forall|i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1_000_000_000,
            forall|q: int|
                0 <= q < queries.len() ==> {
                    let (l1, r1) = #[trigger] queries[q];
                    1 <= l1 && l1 <= r1 && (r1 as int) <= arr.len()
                },
        ensures
            res.len() == queries.len(),
            forall|k: int|
                0 <= k && k < res.len() ==> (#[trigger] res[k] == is_ladder(arr@, (queries[k].0 as int) - 1, (queries[k].1 as int) - 1)),
    {
        let n = arr.len();
        let mut up_end = Vec::new();
        let mut i = 0usize;
        while i < n
            invariant
                n == arr.len(),
                i <= n,
                up_end.len() == i,
            decreases n - i,
        {
            up_end.push(0usize);
            i = i + 1;
        }
        up_end.set(n - 1, n - 1);
        proof {
            assert(up_end[n as int - 1] == n - 1);
            assert(up_end_spec(arr@, n as int - 1) == n as int - 1);
        }
        i = n - 1;
        while i > 0
            invariant
                n == arr.len(),
                up_end.len() == n,
                i < n,
                forall|j: int| i as int <= j && j < n as int ==> up_end[j] as int == up_end_spec(arr@, j),
            decreases i,
        {
            let j = i - 1;
            if arr[j] <= arr[j + 1] {
                let ghost old_up = up_end@;
                let value = up_end[j + 1];
                up_end.set(j, up_end[j + 1]);
                proof {
                    assert(value as int == up_end_spec(arr@, j as int + 1));
                    assert(up_end_spec(arr@, j as int) == up_end_spec(arr@, j as int + 1));
                    assert(up_end@ == old_up.update(j as int, value));
                    assert forall|k: int| j as int <= k && k < n as int implies up_end[k] as int == up_end_spec(arr@, k) by {
                        if k == j as int {
                            assert(up_end[k] == value);
                        } else {
                            assert(j as int + 1 <= k);
                            assert(up_end[k] == old_up[k]);
                        }
                    }
                }
            } else {
                let ghost old_up = up_end@;
                up_end.set(j, j);
                proof {
                    assert(up_end_spec(arr@, j as int) == j as int);
                    assert(up_end@ == old_up.update(j as int, j));
                    assert forall|k: int| j as int <= k && k < n as int implies up_end[k] as int == up_end_spec(arr@, k) by {
                        if k == j as int {
                            assert(up_end[k] == j);
                        } else {
                            assert(j as int + 1 <= k);
                            assert(up_end[k] == old_up[k]);
                        }
                    }
                }
            }
            i = j;
        }
        let mut down_end = Vec::new();
        i = 0;
        while i < n
            invariant
                n == arr.len(),
                i <= n,
                down_end.len() == i,
            decreases n - i,
        {
            down_end.push(0usize);
            i = i + 1;
        }
        down_end.set(n - 1, n - 1);
        proof {
            assert(down_end[n as int - 1] == n - 1);
            assert(down_end_spec(arr@, n as int - 1) == n as int - 1);
        }
        i = n - 1;
        while i > 0
            invariant
                n == arr.len(),
                down_end.len() == n,
                i < n,
                forall|j: int| i as int <= j && j < n as int ==> down_end[j] as int == down_end_spec(arr@, j),
            decreases i,
        {
            let j = i - 1;
            if arr[j] >= arr[j + 1] {
                let ghost old_down = down_end@;
                let value = down_end[j + 1];
                down_end.set(j, down_end[j + 1]);
                proof {
                    assert(value as int == down_end_spec(arr@, j as int + 1));
                    assert(down_end_spec(arr@, j as int) == down_end_spec(arr@, j as int + 1));
                    assert(down_end@ == old_down.update(j as int, value));
                    assert forall|k: int| j as int <= k && k < n as int implies down_end[k] as int == down_end_spec(arr@, k) by {
                        if k == j as int {
                            assert(down_end[k] == value);
                        } else {
                            assert(j as int + 1 <= k);
                            assert(down_end[k] == old_down[k]);
                        }
                    }
                }
            } else {
                let ghost old_down = down_end@;
                down_end.set(j, j);
                proof {
                    assert(down_end_spec(arr@, j as int) == j as int);
                    assert(down_end@ == old_down.update(j as int, j));
                    assert forall|k: int| j as int <= k && k < n as int implies down_end[k] as int == down_end_spec(arr@, k) by {
                        if k == j as int {
                            assert(down_end[k] == j);
                        } else {
                            assert(j as int + 1 <= k);
                            assert(down_end[k] == old_down[k]);
                        }
                    }
                }
            }
            i = j;
        }
        let mut res = Vec::new();
        let mut qi = 0usize;
        while qi < queries.len()
            invariant
                n == arr.len(),
                up_end.len() == n,
                down_end.len() == n,
                forall|j: int| 0 <= j && j < n as int ==> up_end[j] as int == up_end_spec(arr@, j),
                forall|j: int| 0 <= j && j < n as int ==> down_end[j] as int == down_end_spec(arr@, j),
                forall|q: int|
                    0 <= q < queries.len() ==> {
                        let (l1, r1) = #[trigger] queries[q];
                        1 <= l1 && l1 <= r1 && (r1 as int) <= arr.len()
                    },
                qi <= queries.len(),
                res.len() == qi,
                forall|k: int|
                    0 <= k && k < qi ==> (#[trigger] res[k] == is_ladder(arr@, (queries[k].0 as int) - 1, (queries[k].1 as int) - 1)),
            decreases queries.len() - qi,
        {
            let (l1, r1) = queries[qi];
            proof {
                assert(1 <= l1 && l1 <= r1 && (r1 as int) <= arr.len());
            }
            let l = (l1 - 1) as usize;
            let r = (r1 - 1) as usize;
            let peak = up_end[l];
            proof {
                assert(l <= r);
                assert(r < n);
                assert(peak as int == up_end_spec(arr@, l as int));
                lemma_up_end_bounds(arr@, l as int);
                assert(up_end_spec(arr@, l as int) < n as int);
                assert(peak < n);
            }
            let answer = down_end[peak] >= r;
            proof {
                assert(down_end@[peak as int] as int == down_end_spec(arr@, peak as int));
                lemma_is_ladder_iff_bound(arr@, l as int, r as int);
                assert(answer == (r as int <= ladder_end_spec(arr@, l as int)));
                assert(answer == is_ladder(arr@, l as int, r as int));
            }
            let ghost old_res = res@;
            let cur = qi;
            res.push(answer);
            qi = qi + 1;
            proof {
                assert(res@ == old_res.push(answer));
                assert forall|k: int|
                    0 <= k && k < qi implies (#[trigger] res[k] == is_ladder(arr@, (queries[k].0 as int) - 1, (queries[k].1 as int) - 1)) by {
                    if 0 <= k && k < qi {
                        if k == cur as int {
                            assert(res[k] == answer);
                        } else {
                            assert(k < cur as int);
                            assert(k < old_res.len());
                            assert(res[k] == old_res[k]);
                        }
                    }
                }
            }
        }
        res
    }
}

}
