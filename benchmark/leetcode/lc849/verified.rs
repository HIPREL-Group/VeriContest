use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

pub open spec fn run_candidate(n: int, start: int, end: int) -> int {
    let len = end - start;
    if start == 0 || end == n { len } else { (len + 1) / 2 }
}

pub open spec fn is_optimal_seat(seats: Seq<i32>, pos: int, dist: int) -> bool {
    &&& seats[pos] == 0
    &&& forall |q: int| 0 <= q < seats.len() && seats[q] == 1 ==> dist <= #[trigger] abs_diff(pos, q)
    &&& exists |q: int| 0 <= q < seats.len() && seats[q] == 1 && #[trigger] abs_diff(pos, q) == dist
}

pub open spec fn seat_has_person_within(seats: Seq<i32>, pos: int, dist: int) -> bool {
    exists |q: int| 0 <= q < seats.len() && seats[q] == 1 && #[trigger] abs_diff(pos, q) <= dist
}

proof fn lemma_run_candidate_bounds(seats: Seq<i32>, start: int, end: int)
    requires
        2 <= seats.len(),
        0 <= start < end <= seats.len(),
        start == 0 || seats[start - 1] == 1,
        end == seats.len() || seats[end] == 1,
        forall |k: int| 0 <= k < seats.len() ==> 0 <= #[trigger] seats[k] <= 1,
        forall |k: int| start <= k < end ==> seats[k] == 0,
        exists |k: int| 0 <= k < seats.len() && seats[k] == 1,
    ensures
        1 <= run_candidate(seats.len() as int, start, end) <= seats.len() as int - 1,
{
    let len = end - start;
    assert(len >= 1);
    if start == 0 {
        assert(end < seats.len()) by {
            if end == seats.len() {
                assert forall |k: int| 0 <= k < seats.len() implies seats[k] == 0 by {
                };
                let occ = choose |k: int| 0 <= k < seats.len() && seats[k] == 1;
                assert(false);
            }
        };
        assert(run_candidate(seats.len() as int, start, end) == len);
        assert(len <= seats.len() - 1);
    } else if end == seats.len() {
        assert(start > 0);
        assert(len <= seats.len() - 1);
        assert(run_candidate(seats.len() as int, start, end) == len);
    } else {
        assert(len <= seats.len() - 2);
        assert(1 <= (len + 1) / 2);
        assert((len + 1) / 2 <= len);
        assert(len <= seats.len() - 1);
    }
}

proof fn lemma_run_position_bound(seats: Seq<i32>, start: int, end: int, pos: int)
    requires
        2 <= seats.len(),
        0 <= start < end <= seats.len(),
        start <= pos < end,
        start == 0 || seats[start - 1] == 1,
        end == seats.len() || seats[end] == 1,
        forall |k: int| 0 <= k < seats.len() ==> 0 <= #[trigger] seats[k] <= 1,
        forall |k: int| start <= k < end ==> seats[k] == 0,
        exists |k: int| 0 <= k < seats.len() && seats[k] == 1,
    ensures
        seat_has_person_within(seats, pos, run_candidate(seats.len() as int, start, end)),
{
    let n = seats.len();
    let len = end - start;
    let cand = run_candidate(n as int, start, end);
    if start == 0 {
        assert(end < n) by {
            if end == n {
                assert forall |k: int| 0 <= k < n implies seats[k] == 0 by {
                };
                let occ = choose |k: int| 0 <= k < n && seats[k] == 1;
                assert(false);
            }
        };
        assert(seats[end] == 1);
        assert(abs_diff(pos, end) == end - pos);
        assert(end - pos <= len);
        assert(cand == len);
    } else if end == n {
        assert(seats[start - 1] == 1);
        assert(abs_diff(pos, start - 1) == pos - (start - 1));
        assert(pos - (start - 1) <= len);
        assert(cand == len);
    } else {
        assert(seats[start - 1] == 1);
        assert(seats[end] == 1);
        assert(cand == (len + 1) / 2);
        if pos - start + 1 <= cand {
            assert(abs_diff(pos, start - 1) == pos - (start - 1));
        } else {
            assert(pos - start + 1 >= cand + 1);
            assert(end - pos <= cand);
            assert(abs_diff(pos, end) == end - pos);
        }
    }
}

proof fn lemma_run_all_positions_bounded(seats: Seq<i32>, start: int, end: int)
    requires
        2 <= seats.len(),
        0 <= start < end <= seats.len(),
        start == 0 || seats[start - 1] == 1,
        end == seats.len() || seats[end] == 1,
        forall |k: int| 0 <= k < seats.len() ==> 0 <= #[trigger] seats[k] <= 1,
        forall |k: int| start <= k < end ==> seats[k] == 0,
        exists |k: int| 0 <= k < seats.len() && seats[k] == 1,
    ensures
        forall |pos: int| start <= pos < end ==> #[trigger] seat_has_person_within(seats, pos, run_candidate(seats.len() as int, start, end)),
{
    assert forall |pos: int| start <= pos < end implies #[trigger] seat_has_person_within(seats, pos, run_candidate(seats.len() as int, start, end)) by {
        lemma_run_position_bound(seats, start, end, pos);
    };
}

proof fn lemma_run_has_witness(seats: Seq<i32>, start: int, end: int)
    requires
        2 <= seats.len(),
        0 <= start < end <= seats.len(),
        start == 0 || seats[start - 1] == 1,
        end == seats.len() || seats[end] == 1,
        forall |k: int| 0 <= k < seats.len() ==> 0 <= #[trigger] seats[k] <= 1,
        forall |k: int| start <= k < end ==> seats[k] == 0,
        exists |k: int| 0 <= k < seats.len() && seats[k] == 1,
    ensures
        exists |pos: int| start <= pos < end && is_optimal_seat(seats, pos, run_candidate(seats.len() as int, start, end)),
{
    let n = seats.len();
    let len = end - start;
    let cand = run_candidate(n as int, start, end);
    if start == 0 {
        assert(end < n) by {
            if end == n {
                assert forall |k: int| 0 <= k < n implies seats[k] == 0 by {
                };
                let occ = choose |k: int| 0 <= k < n && seats[k] == 1;
                assert(false);
            }
        };
        assert(is_optimal_seat(seats, 0, cand)) by {
            assert(seats[0] == 0);
            assert forall |q: int| 0 <= q < n && seats[q] == 1 implies cand <= #[trigger] abs_diff(0, q) by {
                assert(q >= end) by {
                    if q < end {
                        assert(seats[q] == 0);
                    }
                };
                assert(abs_diff(0, q) == q);
                assert(cand == len);
                assert(q >= len);
            };
            assert(seats[end] == 1);
            assert(abs_diff(0, end) == end);
            assert(cand == len);
        };
    } else if end == n {
        let pos = n - 1;
        assert(is_optimal_seat(seats, pos, cand)) by {
            assert(seats[pos] == 0);
            assert forall |q: int| 0 <= q < n && seats[q] == 1 implies cand <= #[trigger] abs_diff(pos, q) by {
                assert(q < start) by {
                    if start <= q {
                        assert(seats[q] == 0);
                    }
                };
                assert(abs_diff(pos, q) == pos - q);
                assert(cand == len);
                assert(pos - q >= n - start);
            };
            assert(seats[start - 1] == 1);
            assert(abs_diff(pos, start - 1) == pos - (start - 1));
            assert(cand == len);
        };
    } else {
        let pos = start + len / 2;
        assert(start <= pos < end);
        assert(is_optimal_seat(seats, pos, cand)) by {
            assert(seats[pos] == 0);
            assert forall |q: int| 0 <= q < n && seats[q] == 1 implies cand <= #[trigger] abs_diff(pos, q) by {
                if q < start {
                    assert(abs_diff(pos, q) == pos - q);
                    assert(pos - q >= pos - (start - 1));
                } else {
                    assert(q >= end) by {
                        if q < end {
                            assert(seats[q] == 0);
                        }
                    };
                    assert(abs_diff(pos, q) == q - pos);
                    assert(q - pos >= end - pos);
                }
            };
            assert(seats[end] == 1);
            assert(abs_diff(pos, end) == end - pos);
            assert(cand == (len + 1) / 2);
        };
    }
}

impl Solution {
    pub fn max_dist_to_closest(seats: Vec<i32>) -> (result: i32)
        requires
            2 <= seats.len() <= 20_000,
            forall |i: int| 0 <= i < seats.len() ==> 0 <= #[trigger] seats[i] <= 1,
            exists |i: int| 0 <= i < seats.len() && seats[i] == 0,
            exists |i: int| 0 <= i < seats.len() && seats[i] == 1,
        ensures
            1 <= result <= seats.len() - 1,
            exists |pos: int| 0 <= pos < seats.len() && is_optimal_seat(seats@, pos, result as int),
            forall |pos: int| 0 <= pos < seats.len() && seats[pos] == 0 ==> #[trigger] seat_has_person_within(seats@, pos, result as int),
    {
        let n = seats.len();
        let mut i: usize = 0;
        let mut ans: i32 = 0;
        let mut have_witness = false;
        let ghost mut best_pos: int = 0;

        while i < n
            invariant
                n == seats.len(),
                2 <= n <= 20_000,
                0 <= i <= n,
                0 <= ans <= n - 1,
                forall |k: int| 0 <= k < n as int ==> 0 <= #[trigger] seats[k] <= 1,
                exists |k: int| 0 <= k < n as int && seats[k] == 1,
                have_witness <==> exists |pos: int| 0 <= pos < i as int && seats[pos] == 0,
                have_witness ==> 1 <= ans,
                have_witness ==> 0 <= best_pos < i as int,
                have_witness ==> is_optimal_seat(seats@, best_pos, ans as int),
                i < n as usize && seats[i as int] == 0 ==> i == 0 || seats[i as int - 1] == 1,
                forall |pos: int| 0 <= pos < i as int && seats[pos] == 0 ==> #[trigger] seat_has_person_within(seats@, pos, ans as int),
            decreases n - i,
        {
            if seats[i] == 1 {
                i = i + 1;
            } else {
                let start = i;
                while i < n && seats[i] == 0
                    invariant
                        n == seats.len(),
                        2 <= n <= 20_000,
                        0 <= start <= i <= n,
                        start == 0 || seats[start as int - 1] == 1,
                        forall |k: int| 0 <= k < n as int ==> 0 <= #[trigger] seats[k] <= 1,
                        forall |k: int| start as int <= k < i as int ==> seats[k] == 0,
                    decreases n - i,
                {
                    i = i + 1;
                }

                let end = i;
                let len = end - start;
                proof {
                    assert(forall |k: int| start as int <= k < end as int ==> seats[k] == 0);
                    if end < n {
                        assert(seats[end as int] == 1) by {
                            assert(0 <= seats[end as int] <= 1);
                            assert(seats[end as int] != 0);
                        };
                    }
                    if start > 0 {
                        assert(seats[start as int - 1] == 1);
                    }
                }

                let cand = if start == 0 || end == n {
                    len as i32
                } else {
                    ((len + 1) / 2) as i32
                };
                let old_ans = ans;
                let old_have_witness = have_witness;

                proof {
                    lemma_run_candidate_bounds(seats@, start as int, end as int);
                    lemma_run_all_positions_bounded(seats@, start as int, end as int);
                    lemma_run_has_witness(seats@, start as int, end as int);
                }

                if !have_witness || cand > ans {
                    ans = cand;
                    have_witness = true;
                    proof {
                        best_pos = choose |pos: int|
                            start as int <= pos < end as int
                            && is_optimal_seat(seats@, pos, run_candidate(seats.len() as int, start as int, end as int));
                        assert(run_candidate(seats.len() as int, start as int, end as int) == cand as int);
                    }
                } else {
                    have_witness = true;
                }

                proof {
                    assert(have_witness);
                    assert(old_have_witness || exists |pos: int| start as int <= pos < end as int && seats[pos] == 0);
                    assert(have_witness <==> exists |pos: int| 0 <= pos < end as int && seats[pos] == 0) by {
                        assert(exists |pos: int| start as int <= pos < end as int && seats[pos] == 0);
                    };

                    assert forall |pos: int| 0 <= pos < end as int && seats[pos] == 0 implies #[trigger] seat_has_person_within(seats@, pos, ans as int) by {
                        if pos < start as int {
                            assert(seat_has_person_within(seats@, pos, old_ans as int));
                            let q = choose |q: int| 0 <= q < n as int && seats[q] == 1 && abs_diff(pos, q) <= old_ans as int;
                            assert(abs_diff(pos, q) <= ans as int);
                        } else {
                            assert(seat_has_person_within(seats@, pos, run_candidate(seats.len() as int, start as int, end as int)));
                            let q = choose |q: int| 0 <= q < n as int && seats[q] == 1 && abs_diff(pos, q) <= run_candidate(seats.len() as int, start as int, end as int);
                            assert(run_candidate(seats.len() as int, start as int, end as int) <= ans as int);
                            assert(abs_diff(pos, q) <= ans as int);
                        }
                    };
                }
            }
        }

        proof {
            assert(have_witness) by {
                let pos = choose |pos: int| 0 <= pos < n as int && seats[pos] == 0;
                assert(0 <= pos < n as int);
            };
        }

        ans
    }
}

}
