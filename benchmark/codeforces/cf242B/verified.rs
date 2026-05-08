use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn segment_contains(left: Seq<i32>, right: Seq<i32>, i: int, j: int) -> bool
    recommends
        left.len() == right.len(),
        0 <= i < left.len(),
        0 <= j < left.len(),
{
    left[i] <= left[j] && right[j] <= right[i]
}

pub open spec fn covers_all_segments(left: Seq<i32>, right: Seq<i32>, i: int) -> bool
    recommends
        left.len() == right.len(),
        0 <= i < left.len(),
{
    forall|j: int| 0 <= j < left.len() ==> #[trigger] segment_contains(left, right, i, j)
}

pub open spec fn same_left(left: Seq<i32>, i: int, j: int) -> bool
    recommends
        0 <= i < left.len(),
        0 <= j < left.len(),
{
    left[i] == left[j]
}

pub open spec fn better_candidate(left: Seq<i32>, right: Seq<i32>, new_idx: int, old_idx: int) -> bool
    recommends
        left.len() == right.len(),
        0 <= new_idx < left.len(),
        0 <= old_idx < left.len(),
{
    left[new_idx] < left[old_idx] || (left[new_idx] == left[old_idx] && right[old_idx] < right[new_idx])
}

pub open spec fn candidate_is_min_left(left: Seq<i32>, candidate: int, bound: int) -> bool
    recommends
        0 <= candidate < bound <= left.len(),
{
    forall|j: int| 0 <= j < bound ==> left[candidate] <= #[trigger] left[j]
}

pub open spec fn candidate_is_max_right_with_min_left(left: Seq<i32>, right: Seq<i32>, candidate: int, bound: int) -> bool
    recommends
        left.len() == right.len(),
        0 <= candidate < bound <= left.len(),
{
    forall|j: int| 0 <= j < bound && #[trigger] same_left(left, candidate, j) ==> right[j] <= right[candidate]
}

proof fn lemma_keep_candidate(left: Seq<i32>, right: Seq<i32>, candidate: int, bound: int)
    requires
        left.len() == right.len(),
        0 <= candidate < bound < left.len(),
        candidate_is_min_left(left, candidate, bound),
        candidate_is_max_right_with_min_left(left, right, candidate, bound),
        !better_candidate(left, right, bound, candidate),
    ensures
        candidate_is_min_left(left, candidate, bound + 1),
        candidate_is_max_right_with_min_left(left, right, candidate, bound + 1),
{
    assert forall|j: int| 0 <= j < bound + 1 implies left[candidate] <= #[trigger] left[j] by {
        if j < bound {
        } else {
            assert(j == bound);
            assert(!(left[bound] < left[candidate] || (left[bound] == left[candidate] && right[candidate] < right[bound])));
            if left[bound] < left[candidate] {
                assert(false);
            }
        }
    }
    assert forall|j: int| 0 <= j < bound + 1 && #[trigger] same_left(left, candidate, j) implies right[j] <= right[candidate] by {
        if j < bound {
        } else {
            assert(j == bound);
            assert(left[bound] == left[candidate]);
            assert(!(left[bound] < left[candidate] || (left[bound] == left[candidate] && right[candidate] < right[bound])));
            if right[candidate] < right[bound] {
                assert(left[bound] == left[candidate] && right[candidate] < right[bound]);
                assert(false);
            }
        }
    }
}

proof fn lemma_take_new_candidate(left: Seq<i32>, right: Seq<i32>, old_candidate: int, bound: int)
    requires
        left.len() == right.len(),
        0 <= old_candidate < bound < left.len(),
        candidate_is_min_left(left, old_candidate, bound),
        candidate_is_max_right_with_min_left(left, right, old_candidate, bound),
        better_candidate(left, right, bound, old_candidate),
    ensures
        candidate_is_min_left(left, bound, bound + 1),
        candidate_is_max_right_with_min_left(left, right, bound, bound + 1),
{
    assert forall|j: int| 0 <= j < bound + 1 implies left[bound] <= #[trigger] left[j] by {
        if j < bound {
            assert(left[old_candidate] <= left[j]);
            if left[bound] < left[old_candidate] {
            } else {
                assert(left[bound] == left[old_candidate]);
            }
        } else {
            assert(j == bound);
        }
    }
    assert forall|j: int| 0 <= j < bound + 1 && #[trigger] same_left(left, bound, j) implies right[j] <= right[bound] by {
        if j < bound {
            assert(left[j] == left[bound]);
            assert(left[old_candidate] <= left[j]);
            if left[bound] < left[old_candidate] {
                assert(left[old_candidate] <= left[bound]);
                assert(false);
            }
            assert(left[bound] == left[old_candidate]);
            assert(same_left(left, old_candidate, j));
            assert(right[j] <= right[old_candidate]);
            assert(better_candidate(left, right, bound, old_candidate));
            assert(right[old_candidate] < right[bound]);
        } else {
            assert(j == bound);
        }
    }
}

proof fn lemma_covering_implies_candidate_covering(left: Seq<i32>, right: Seq<i32>, candidate: int, big: int)
    requires
        left.len() == right.len(),
        0 <= candidate < left.len(),
        0 <= big < left.len(),
        candidate_is_min_left(left, candidate, left.len() as int),
        candidate_is_max_right_with_min_left(left, right, candidate, left.len() as int),
        covers_all_segments(left, right, big),
    ensures
        covers_all_segments(left, right, candidate),
{
    assert(left[candidate] <= left[big]);
    assert(segment_contains(left, right, big, candidate));
    assert(left[big] <= left[candidate]);
    assert(left[big] == left[candidate]);
    assert(same_left(left, candidate, big));
    assert(right[big] <= right[candidate]);
    assert forall|j: int| 0 <= j < left.len() implies #[trigger] segment_contains(left, right, candidate, j) by {
        assert(segment_contains(left, right, big, j));
        assert(left[candidate] <= left[big]);
        assert(left[big] <= left[j]);
        assert(right[j] <= right[big]);
        assert(right[big] <= right[candidate]);
    }
}

impl Solution {
    pub fn find_covering_segment(left: Vec<i32>, right: Vec<i32>) -> (ans: i32)
        requires
            left.len() == right.len(),
            1 <= left.len() <= 100_000,
            forall|i: int| 0 <= i < left.len() ==> 1 <= #[trigger] left[i] <= right[i] <= 1_000_000_000,
            forall|i: int, j: int|
                0 <= i < j < left.len() ==> left[i] != left[j] || right[i] != right[j],
        ensures
            0 <= ans <= left.len(),
            ans != 0 ==> covers_all_segments(left@, right@, ans as int - 1),
            ans == 0 ==> forall|i: int| 0 <= i < left.len() ==> !covers_all_segments(left@, right@, i),
    {
        let mut candidate = 0usize;
        let mut i = 1usize;
        while i < left.len()
            invariant
                left.len() == right.len(),
                1 <= left.len() <= 100_000,
                forall|k: int| 0 <= k < left.len() ==> 1 <= #[trigger] left[k] <= right[k] <= 1_000_000_000,
                forall|a: int, b: int| 0 <= a < b < left.len() ==> left[a] != left[b] || right[a] != right[b],
                1 <= i <= left.len(),
                0 <= candidate < i,
                candidate_is_min_left(left@, candidate as int, i as int),
                candidate_is_max_right_with_min_left(left@, right@, candidate as int, i as int),
            decreases left.len() - i,
        {
            let old_candidate = candidate;
            if left[i] < left[candidate] || (left[i] == left[candidate] && right[candidate] < right[i]) {
                proof {
                    lemma_take_new_candidate(left@, right@, candidate as int, i as int);
                }
                candidate = i;
            } else {
                proof {
                    lemma_keep_candidate(left@, right@, candidate as int, i as int);
                }
            }
            i += 1;
            proof {
                if candidate == old_candidate {
                    assert(candidate_is_min_left(left@, candidate as int, i as int));
                    assert(candidate_is_max_right_with_min_left(left@, right@, candidate as int, i as int));
                } else {
                    assert(candidate == i - 1);
                    assert(candidate_is_min_left(left@, candidate as int, i as int));
                    assert(candidate_is_max_right_with_min_left(left@, right@, candidate as int, i as int));
                }
            }
        }

        let mut j = 0usize;
        while j < left.len()
            invariant
                left.len() == right.len(),
                1 <= left.len() <= 100_000,
                forall|k: int| 0 <= k < left.len() ==> 1 <= #[trigger] left[k] <= right[k] <= 1_000_000_000,
                forall|a: int, b: int| 0 <= a < b < left.len() ==> left[a] != left[b] || right[a] != right[b],
                0 <= candidate < left.len(),
                candidate_is_min_left(left@, candidate as int, left.len() as int),
                candidate_is_max_right_with_min_left(left@, right@, candidate as int, left.len() as int),
                0 <= j <= left.len(),
                forall|k: int| 0 <= k < j ==> #[trigger] segment_contains(left@, right@, candidate as int, k),
            decreases left.len() - j,
        {
            if left[candidate] > left[j] || right[j] > right[candidate] {
                proof {
                    assert(left[candidate as int] <= left[j as int]);
                    assert(!segment_contains(left@, right@, candidate as int, j as int));
                    assert forall|k: int| 0 <= k < left.len() implies !covers_all_segments(left@, right@, k) by {
                        if covers_all_segments(left@, right@, k) {
                            lemma_covering_implies_candidate_covering(left@, right@, candidate as int, k);
                            assert(segment_contains(left@, right@, candidate as int, j as int));
                        }
                    }
                }
                return 0;
            }
            proof {
                assert(segment_contains(left@, right@, candidate as int, j as int));
            }
            j += 1;
        }

        proof {
            assert(forall|k: int| 0 <= k < left.len() ==> #[trigger] segment_contains(left@, right@, candidate as int, k));
            assert(covers_all_segments(left@, right@, candidate as int));
        }
        candidate as i32 + 1
    }
}

}
