use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b {
        a - b
    } else {
        b - a
    }
}

pub open spec fn min_distance_to_other(x: Seq<i64>, i: int) -> int
    recommends
        0 <= i < x.len(),
        x.len() >= 2,
{
    if i == 0 {
        abs_diff(x[1] as int, x[0] as int)
    } else if i == x.len() - 1 {
        abs_diff(x[i] as int, x[i - 1] as int)
    } else {
        let left = abs_diff(x[i] as int, x[i - 1] as int);
        let right = abs_diff(x[i + 1] as int, x[i] as int);
        if left <= right { left } else { right }
    }
}

pub open spec fn max_distance_to_other(x: Seq<i64>, i: int) -> int
    recommends
        0 <= i < x.len(),
        x.len() >= 2,
{
    let left = abs_diff(x[i] as int, x[0] as int);
    let right = abs_diff(x[x.len() - 1] as int, x[i] as int);
    if left >= right { left } else { right }
}

proof fn lemma_min_distance_properties(x: Seq<i64>, i: int)
    requires
        0 <= i < x.len(),
        x.len() >= 2,
        forall |a: int, b: int| 0 <= a < b < x.len() ==> x[a] < x[b],
    ensures
        forall |j: int| 0 <= j < x.len() && j != i ==> abs_diff(x[i] as int, x[j] as int) >= min_distance_to_other(x, i),
        exists |j: int| 0 <= j < x.len() && j != i && abs_diff(x[i] as int, x[j] as int) == min_distance_to_other(x, i),
{
    if i == 0 {
        assert forall |j: int| 0 <= j < x.len() && j != i implies abs_diff(x[i] as int, x[j] as int) >= min_distance_to_other(x, i) by {
            if j == 1 {
                assert(abs_diff(x[i] as int, x[j] as int) == min_distance_to_other(x, i));
            } else {
                assert(j > 1);
                assert(x[0] < x[1] < x[j]);
                assert(abs_diff(x[i] as int, x[j] as int) > abs_diff(x[1] as int, x[0] as int));
            }
        }
        assert(exists |j: int| 0 <= j < x.len() && j != i && abs_diff(x[i] as int, x[j] as int) == min_distance_to_other(x, i)) by {
            assert(abs_diff(x[0] as int, x[1] as int) == min_distance_to_other(x, 0));
        }
    } else if i == x.len() - 1 {
        assert forall |j: int| 0 <= j < x.len() && j != i implies abs_diff(x[i] as int, x[j] as int) >= min_distance_to_other(x, i) by {
            if j == i - 1 {
                assert(abs_diff(x[i] as int, x[j] as int) == min_distance_to_other(x, i));
            } else {
                assert(j < i - 1);
                assert(x[j] < x[i - 1] < x[i]);
                assert(abs_diff(x[i] as int, x[j] as int) > abs_diff(x[i] as int, x[i - 1] as int));
            }
        }
        assert(exists |j: int| 0 <= j < x.len() && j != i && abs_diff(x[i] as int, x[j] as int) == min_distance_to_other(x, i)) by {
            assert(abs_diff(x[i] as int, x[i - 1] as int) == min_distance_to_other(x, i));
        }
    } else {
        assert forall |j: int| 0 <= j < x.len() && j != i implies abs_diff(x[i] as int, x[j] as int) >= min_distance_to_other(x, i) by {
            if j == i - 1 || j == i + 1 {
                assert(abs_diff(x[i] as int, x[j] as int) >= min_distance_to_other(x, i));
            } else if j < i - 1 {
                assert(x[j] < x[i - 1] < x[i]);
                assert(abs_diff(x[i] as int, x[j] as int) > abs_diff(x[i] as int, x[i - 1] as int));
                assert(abs_diff(x[i] as int, x[j] as int) >= min_distance_to_other(x, i));
            } else {
                assert(j > i + 1);
                assert(x[i] < x[i + 1] < x[j]);
                assert(abs_diff(x[i] as int, x[j] as int) > abs_diff(x[i + 1] as int, x[i] as int));
                assert(abs_diff(x[i] as int, x[j] as int) >= min_distance_to_other(x, i));
            }
        }
        assert(exists |j: int| 0 <= j < x.len() && j != i && abs_diff(x[i] as int, x[j] as int) == min_distance_to_other(x, i)) by {
            if abs_diff(x[i] as int, x[i - 1] as int) <= abs_diff(x[i + 1] as int, x[i] as int) {
                assert(abs_diff(x[i] as int, x[i - 1] as int) == min_distance_to_other(x, i));
            } else {
                assert(abs_diff(x[i + 1] as int, x[i] as int) == min_distance_to_other(x, i));
            }
        }
    }
}

proof fn lemma_max_distance_properties(x: Seq<i64>, i: int)
    requires
        0 <= i < x.len(),
        x.len() >= 2,
        forall |a: int, b: int| 0 <= a < b < x.len() ==> x[a] < x[b],
    ensures
        forall |j: int| 0 <= j < x.len() && j != i ==> abs_diff(x[i] as int, x[j] as int) <= max_distance_to_other(x, i),
        exists |j: int| 0 <= j < x.len() && j != i && abs_diff(x[i] as int, x[j] as int) == max_distance_to_other(x, i),
    {
    let left_end = abs_diff(x[i] as int, x[0] as int);
    let right_end = abs_diff(x[x.len() - 1] as int, x[i] as int);
    assert forall |j: int| 0 <= j < x.len() && j != i implies abs_diff(x[i] as int, x[j] as int) <= max_distance_to_other(x, i) by {
        if j == 0 {
            assert(abs_diff(x[i] as int, x[j] as int) == left_end);
            assert(left_end <= max_distance_to_other(x, i));
        } else if j == x.len() - 1 {
            assert(abs_diff(x[i] as int, x[j] as int) == right_end);
            assert(right_end <= max_distance_to_other(x, i));
        } else {
            assert(0 < j < x.len() - 1);
            assert(x[0] < x[j] < x[x.len() - 1]);
            if x[i] <= x[j] {
                assert(abs_diff(x[i] as int, x[j] as int) == x[j] as int - x[i] as int);
                assert(x[j] as int - x[i] as int <= x[x.len() - 1] as int - x[i] as int);
                assert(abs_diff(x[i] as int, x[j] as int) <= right_end);
            } else {
                assert(abs_diff(x[i] as int, x[j] as int) == x[i] as int - x[j] as int);
                assert(x[i] as int - x[j] as int <= x[i] as int - x[0] as int);
                assert(abs_diff(x[i] as int, x[j] as int) <= left_end);
            }
            assert(abs_diff(x[i] as int, x[j] as int) <= max_distance_to_other(x, i));
        }
    }
    assert(exists |j: int| 0 <= j < x.len() && j != i && abs_diff(x[i] as int, x[j] as int) == max_distance_to_other(x, i)) by {
        if left_end >= right_end {
            assert(abs_diff(x[i] as int, x[0] as int) == max_distance_to_other(x, i));
        } else {
            assert(abs_diff(x[x.len() - 1] as int, x[i] as int) == max_distance_to_other(x, i));
        }
    }
}

impl Solution {
    pub fn compute_min_max_distances(x: Vec<i64>) -> (result: Vec<(i64, i64)>)
        requires
            2 <= x.len() <= 100_000,
            forall |i: int, j: int| 0 <= i < j < x.len() ==> #[trigger] x[i] < #[trigger] x[j],
            forall |i: int| 0 <= i < x.len() ==> -1_000_000_000 <= #[trigger] x[i] <= 1_000_000_000,
        ensures
            result.len() == x.len(),
            forall |i: int|
                0 <= i < result.len() ==>
                    result[i].0 as int == min_distance_to_other(x@, i)
                    && result[i].1 as int == max_distance_to_other(x@, i)
                    && forall |j: int|
                        0 <= j < x.len() && j != i ==>
                            abs_diff(x[i] as int, x[j] as int) >= min_distance_to_other(x@, i)
                    && exists |j: int|
                        0 <= j < x.len() && j != i &&
                        abs_diff(x[i] as int, x[j] as int) == min_distance_to_other(x@, i)
                    && forall |j: int|
                        0 <= j < x.len() && j != i ==>
                            abs_diff(x[i] as int, x[j] as int) <= max_distance_to_other(x@, i)
                    && exists |j: int|
                        0 <= j < x.len() && j != i &&
                        abs_diff(x[i] as int, x[j] as int) == max_distance_to_other(x@, i),
    {
        let n = x.len();
        let mut result: Vec<(i64, i64)> = Vec::new();
        let mut i = 0usize;
        proof {
            assert(n as int == x@.len());
        }
        while i < n
            invariant
                2 <= n <= 100_000,
                n as int == x@.len(),
                forall |a: int, b: int| 0 <= a < b < x@.len() ==> x@[a] < x@[b],
                forall |a: int| 0 <= a < x@.len() ==> -1_000_000_000 <= #[trigger] x@[a] <= 1_000_000_000,
                0 <= i <= n,
                result.len() == i,
                forall |k: int|
                    0 <= k < result.len() ==>
                        result[k].0 as int == min_distance_to_other(x@, k)
                        && result[k].1 as int == max_distance_to_other(x@, k),
            decreases n - i,
        {
            let mini;
            let maxi;
            proof {
                lemma_min_distance_properties(x@, i as int);
                lemma_max_distance_properties(x@, i as int);
            }
            if i == 0 {
                let d1 = if x[1] >= x[0] { x[1] - x[0] } else { x[0] - x[1] };
                let d2 = if x[n - 1] >= x[0] { x[n - 1] - x[0] } else { x[0] - x[n - 1] };
                mini = d1;
                maxi = d2;
                proof {
                    assert(x[1] >= x[0]);
                    assert(x[n - 1] >= x[0]);
                    assert(mini as int == abs_diff(x[1] as int, x[0] as int));
                    assert(maxi as int == abs_diff(x[n - 1] as int, x[0] as int));
                    assert(mini as int == min_distance_to_other(x@, 0));
                    assert(maxi as int == max_distance_to_other(x@, 0));
                }
            } else if i == n - 1 {
                let d1 = if x[n - 1] >= x[n - 2] { x[n - 1] - x[n - 2] } else { x[n - 2] - x[n - 1] };
                let d2 = if x[n - 1] >= x[0] { x[n - 1] - x[0] } else { x[0] - x[n - 1] };
                mini = d1;
                maxi = d2;
                proof {
                    assert(x[n - 1] >= x[n - 2]);
                    assert(x[n - 1] >= x[0]);
                    assert(mini as int == abs_diff(x[n - 1] as int, x[n - 2] as int));
                    assert(maxi as int == abs_diff(x[n - 1] as int, x[0] as int));
                    assert(mini as int == min_distance_to_other(x@, (n - 1) as int));
                    assert(maxi as int == max_distance_to_other(x@, (n - 1) as int));
                }
            } else {
                let left_dist = if x[i] >= x[i - 1] { x[i] - x[i - 1] } else { x[i - 1] - x[i] };
                let right_dist = if x[i + 1] >= x[i] { x[i + 1] - x[i] } else { x[i] - x[i + 1] };
                mini = left_dist.min(right_dist);
                let left_end = if x[i] >= x[0] { x[i] - x[0] } else { x[0] - x[i] };
                let right_end = if x[n - 1] >= x[i] { x[n - 1] - x[i] } else { x[i] - x[n - 1] };
                maxi = left_end.max(right_end);
                proof {
                    assert(x@[i as int] >= x@[(i - 1) as int]);
                    assert(x@[(i + 1) as int] >= x@[i as int]);
                    assert(x@[i as int] >= x@[0]);
                    assert(x@[(n - 1) as int] >= x@[i as int]);
                    assert(left_dist as int == abs_diff(x@[i as int] as int, x@[(i - 1) as int] as int));
                    assert(right_dist as int == abs_diff(x@[(i + 1) as int] as int, x@[i as int] as int));
                    assert(left_end as int == abs_diff(x@[i as int] as int, x@[0] as int));
                    assert(right_end as int == abs_diff(x@[(n - 1) as int] as int, x@[i as int] as int));
                    assert(mini as int == min_distance_to_other(x@, (i as int)));
                    assert(maxi as int == max_distance_to_other(x@, (i as int)));
                }
            }
            let ghost old_result = result@;
            result.push((mini, maxi));
            proof {
                assert(result@ == old_result.push((mini, maxi)));
                assert forall |k: int| 0 <= k < result.len() implies result[k].0 as int == min_distance_to_other(x@, k) && result[k].1 as int == max_distance_to_other(x@, k) by {
                    if k == i as int {
                        assert(result[k] == (mini, maxi));
                    } else {
                        assert(k < i as int);
                        assert(result[k] == old_result[k]);
                    }
                }
            }
            i += 1;
        }
        proof {
            assert(i == n);
            assert(result.len() == x.len());
            assert forall |i: int| 0 <= i < result.len() implies result[i].0 as int == min_distance_to_other(x@, i) && result[i].1 as int == max_distance_to_other(x@, i) by {
            }
            assert forall |i: int, j: int| 0 <= i < result.len() && 0 <= j < x@.len() && j != i implies abs_diff(x@[i] as int, x@[j] as int) >= min_distance_to_other(x@, i) by {
                if 0 <= i < result.len() && 0 <= j < x@.len() && j != i {
                    lemma_min_distance_properties(x@, i);
                }
            }
            assert forall |i: int| 0 <= i < result.len() implies exists |j: int| 0 <= j < x@.len() && j != i && #[trigger] abs_diff(x@[i] as int, x@[j] as int) == #[trigger] min_distance_to_other(x@, i) by {
                if 0 <= i < result.len() {
                    lemma_min_distance_properties(x@, i);
                }
            }
            assert forall |i: int, j: int| 0 <= i < result.len() && 0 <= j < x@.len() && j != i implies abs_diff(x@[i] as int, x@[j] as int) <= max_distance_to_other(x@, i) by {
                if 0 <= i < result.len() && 0 <= j < x@.len() && j != i {
                    lemma_max_distance_properties(x@, i);
                }
            }
            assert forall |i: int| 0 <= i < result.len() implies exists |j: int| 0 <= j < x@.len() && j != i && #[trigger] abs_diff(x@[i] as int, x@[j] as int) == #[trigger] max_distance_to_other(x@, i) by {
                if 0 <= i < result.len() {
                    lemma_max_distance_properties(x@, i);
                }
            }
        }
        result
    }
}

}
