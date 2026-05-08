use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn trip_load_at(trip: Vec<i32>, stop: int) -> int
        recommends
            trip@.len() == 3,
    {
        if trip@[1] as int <= stop && stop < trip@[2] as int {
            trip@[0] as int
        } else {
            0
        }
    }

    pub open spec fn load_prefix(trips: Seq<Vec<i32>>, n: int, stop: int) -> int
        recommends
            0 <= n <= trips.len(),
            0 <= stop <= 1000,
            forall |i: int| 0 <= i < trips.len() ==> #[trigger] trips[i]@.len() == 3,
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::load_prefix(trips, n - 1, stop) + Self::trip_load_at(trips[n - 1], stop)
        }
    }

    pub open spec fn trip_delta_at(trip: Vec<i32>, stop: int) -> int
        recommends
            trip@.len() == 3,
    {
        (if trip@[1] as int == stop { trip@[0] as int } else { 0 })
            - (if trip@[2] as int == stop { trip@[0] as int } else { 0 })
    }

    pub open spec fn delta_prefix(trips: Seq<Vec<i32>>, n: int, stop: int) -> int
        recommends
            0 <= n <= trips.len(),
            0 <= stop <= 1000,
            forall |i: int| 0 <= i < trips.len() ==> #[trigger] trips[i]@.len() == 3,
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::delta_prefix(trips, n - 1, stop) + Self::trip_delta_at(trips[n - 1], stop)
        }
    }

    proof fn lemma_load_step(trips: Seq<Vec<i32>>, n: int, stop: int)
        requires
            0 <= n <= trips.len(),
            0 <= stop <= 1000,
            forall |i: int| 0 <= i < trips.len() ==> #[trigger] trips[i]@.len() == 3,
            forall |i: int| 0 <= i < trips.len() ==> 1 <= #[trigger] trips[i]@[0] <= 100,
            forall |i: int| 0 <= i < trips.len() ==> 0 <= #[trigger] trips[i]@[1] < trips[i]@[2] <= 1000,
        ensures
            stop == 0 ==> Self::load_prefix(trips, n, stop) == Self::delta_prefix(trips, n, stop),
            stop > 0 ==> Self::load_prefix(trips, n, stop)
                == Self::load_prefix(trips, n, stop - 1) + Self::delta_prefix(trips, n, stop),
        decreases n,
    {
        if n > 0 {
            Self::lemma_load_step(trips, n - 1, stop);
            let trip = trips[n - 1];
            let from = trip@[1] as int;
            let to = trip@[2] as int;
            let passengers = trip@[0] as int;

            assert(Self::load_prefix(trips, n, stop) == Self::load_prefix(trips, n - 1, stop) + Self::trip_load_at(trip, stop));
            assert(Self::delta_prefix(trips, n, stop) == Self::delta_prefix(trips, n - 1, stop) + Self::trip_delta_at(trip, stop));

            if stop == 0 {
                assert(0 <= from < to <= 1000);
                if from == 0 {
                    assert(Self::trip_load_at(trip, stop) == passengers);
                    assert(Self::trip_delta_at(trip, stop) == passengers);
                } else {
                    assert(0 < from);
                    assert(Self::trip_load_at(trip, stop) == 0);
                    assert(Self::trip_delta_at(trip, stop) == 0);
                }
            } else {
                assert(0 < stop <= 1000);
                if stop < from {
                    assert(Self::trip_load_at(trip, stop - 1) == 0);
                    assert(Self::trip_load_at(trip, stop) == 0);
                    assert(Self::trip_delta_at(trip, stop) == 0);
                } else if stop == from {
                    assert(Self::trip_load_at(trip, stop - 1) == 0);
                    assert(Self::trip_load_at(trip, stop) == passengers);
                    assert(Self::trip_delta_at(trip, stop) == passengers);
                } else if stop < to {
                    assert(from < stop < to);
                    assert(Self::trip_load_at(trip, stop - 1) == passengers);
                    assert(Self::trip_load_at(trip, stop) == passengers);
                    assert(Self::trip_delta_at(trip, stop) == 0);
                } else if stop == to {
                    assert(from < stop);
                    assert(Self::trip_load_at(trip, stop - 1) == passengers);
                    assert(Self::trip_load_at(trip, stop) == 0);
                    assert(Self::trip_delta_at(trip, stop) == -passengers);
                } else {
                    assert(to < stop);
                    assert(Self::trip_load_at(trip, stop - 1) == 0);
                    assert(Self::trip_load_at(trip, stop) == 0);
                    assert(Self::trip_delta_at(trip, stop) == 0);
                }
            }
        }
    }

    proof fn lemma_delta_bound(trips: Seq<Vec<i32>>, n: int, stop: int)
        requires
            0 <= n <= trips.len(),
            0 <= stop <= 1000,
            forall |i: int| 0 <= i < trips.len() ==> #[trigger] trips[i]@.len() == 3,
            forall |i: int| 0 <= i < trips.len() ==> 1 <= #[trigger] trips[i]@[0] <= 100,
            forall |i: int| 0 <= i < trips.len() ==> 0 <= #[trigger] trips[i]@[1] < trips[i]@[2] <= 1000,
        ensures
            -(100 * n) <= Self::delta_prefix(trips, n, stop) <= 100 * n,
        decreases n,
    {
        if n > 0 {
            Self::lemma_delta_bound(trips, n - 1, stop);
            let trip = trips[n - 1];
            let passengers = trip@[0] as int;
            assert(Self::delta_prefix(trips, n, stop) == Self::delta_prefix(trips, n - 1, stop) + Self::trip_delta_at(trip, stop));
            if trip@[1] as int == stop {
                assert(Self::trip_delta_at(trip, stop) == passengers);
            } else if trip@[2] as int == stop {
                assert(Self::trip_delta_at(trip, stop) == -passengers);
            } else {
                assert(Self::trip_delta_at(trip, stop) == 0);
            }
        }
    }

    proof fn lemma_load_bound(trips: Seq<Vec<i32>>, n: int, stop: int)
        requires
            0 <= n <= trips.len(),
            0 <= stop <= 1000,
            forall |i: int| 0 <= i < trips.len() ==> #[trigger] trips[i]@.len() == 3,
            forall |i: int| 0 <= i < trips.len() ==> 1 <= #[trigger] trips[i]@[0] <= 100,
            forall |i: int| 0 <= i < trips.len() ==> 0 <= #[trigger] trips[i]@[1] < trips[i]@[2] <= 1000,
        ensures
            0 <= Self::load_prefix(trips, n, stop) <= 100 * n,
        decreases n,
    {
        if n > 0 {
            Self::lemma_load_bound(trips, n - 1, stop);
            let trip = trips[n - 1];
            let passengers = trip@[0] as int;
            assert(Self::load_prefix(trips, n, stop) == Self::load_prefix(trips, n - 1, stop) + Self::trip_load_at(trip, stop));
            if trip@[1] as int <= stop && stop < trip@[2] as int {
                assert(Self::trip_load_at(trip, stop) == passengers);
            } else {
                assert(Self::trip_load_at(trip, stop) == 0);
            }
        }
    }

    pub fn car_pooling(trips: Vec<Vec<i32>>, capacity: i32) -> (result: bool)
        requires
            1 <= trips.len() <= 1000,
            1 <= capacity <= 100_000,
            forall |i: int| 0 <= i < trips.len() ==> #[trigger] trips[i]@.len() == 3,
            forall |i: int| 0 <= i < trips.len() ==> 1 <= #[trigger] trips[i][0] <= 100,
            forall |i: int| 0 <= i < trips.len() ==> 0 <= #[trigger] trips[i][1] < trips[i][2] <= 1000,
        ensures
            result == (forall |stop: int| 0 <= stop <= 1000 ==> #[trigger] Self::load_prefix(trips@, trips.len() as int, stop) <= capacity as int),
    {
        let mut diff: Vec<i64> = Vec::new();
        let mut fill = 0usize;

        while fill < 1001
            invariant
                0 <= fill <= 1001,
                diff.len() == fill,
                forall |k: int| 0 <= k < fill ==> #[trigger] diff@[k] == 0,
            decreases 1001 - fill,
        {
            diff.push(0);
            fill += 1;
        }

        let mut i = 0usize;
        while i < trips.len()
            invariant
                1 <= trips.len() <= 1000,
                1 <= capacity <= 100_000,
                forall |k: int| 0 <= k < trips.len() ==> #[trigger] trips[k]@.len() == 3,
                forall |k: int| 0 <= k < trips.len() ==> 1 <= #[trigger] trips[k][0] <= 100,
                forall |k: int| 0 <= k < trips.len() ==> 0 <= #[trigger] trips[k][1] < trips[k][2] <= 1000,
                0 <= i <= trips.len(),
                diff.len() == 1001,
                forall |stop: int| 0 <= stop <= 1000 ==> #[trigger] diff@[stop] as int == Self::delta_prefix(trips@, i as int, stop),
            decreases trips.len() - i,
        {
            proof {
                assert(trips[i as int]@.len() == 3);
                assert(0 <= trips[i as int][1] < trips[i as int][2] <= 1000);
            }

            let passengers = trips[i][0] as i64;
            let from = trips[i][1] as usize;
            let to = trips[i][2] as usize;
            proof {
                let idx = i as int;
                Self::lemma_delta_bound(trips@, idx, from as int);
                Self::lemma_delta_bound(trips@, idx, to as int);
                assert(diff@[from as int] as int == Self::delta_prefix(trips@, idx, from as int));
                assert(diff@[to as int] as int == Self::delta_prefix(trips@, idx, to as int));
                assert(-100 * idx <= diff@[from as int] as int <= 100 * idx);
                assert(-100 * idx <= diff@[to as int] as int <= 100 * idx);
                assert(1 <= passengers as int <= 100);
                assert(-100_100 <= diff@[from as int] as int + passengers as int <= 100_100) by (nonlinear_arith)
                    requires
                        -100 * idx <= diff@[from as int] as int <= 100 * idx,
                        1 <= passengers as int <= 100,
                        idx <= 1000
                {}
                assert(-100_100 <= diff@[to as int] as int - passengers as int <= 100_100) by (nonlinear_arith)
                    requires
                        -100 * idx <= diff@[to as int] as int <= 100 * idx,
                        1 <= passengers as int <= 100,
                        idx <= 1000
                {}
            }
            let add_value = diff[from] + passengers;
            let sub_value = diff[to] - passengers;
            let ghost before = diff@;

            diff.set(from, add_value);
            let ghost after_add = diff@;
            diff.set(to, sub_value);

            proof {
                let idx = i as int;
                assert(0 <= from < 1001);
                assert(0 <= to < 1001);
                assert(from < to);
                assert(after_add == before.update(from as int, add_value));
                assert(diff@ == after_add.update(to as int, sub_value));

                assert forall |stop: int| 0 <= stop <= 1000 implies #[trigger] diff@[stop] as int == Self::delta_prefix(trips@, idx + 1, stop) by {
                    assert(Self::delta_prefix(trips@, idx + 1, stop)
                        == Self::delta_prefix(trips@, idx, stop) + Self::trip_delta_at(trips[idx], stop));
                    if stop == from as int {
                        assert(to as int != stop);
                        assert(after_add[stop] == before[stop] + passengers);
                        assert(diff@[stop] == after_add[stop]);
                        assert(Self::trip_delta_at(trips[idx], stop) == trips[idx]@[0] as int);
                    } else if stop == to as int {
                        assert(from as int != stop);
                        assert(after_add[stop] == before[stop]);
                        assert(diff@[stop] == after_add[stop] - passengers);
                        assert(Self::trip_delta_at(trips[idx], stop) == -(trips[idx]@[0] as int));
                    } else {
                        assert(after_add[stop] == before[stop]);
                        assert(diff@[stop] == after_add[stop]);
                        assert(Self::trip_delta_at(trips[idx], stop) == 0);
                    }
                };
            }

            i += 1;
        }

        let mut current = 0i64;
        let mut stop = 0usize;
        while stop < 1001
            invariant
                1 <= trips.len() <= 1000,
                1 <= capacity <= 100_000,
                forall |k: int| 0 <= k < trips.len() ==> #[trigger] trips[k]@.len() == 3,
                forall |k: int| 0 <= k < trips.len() ==> 1 <= #[trigger] trips[k][0] <= 100,
                forall |k: int| 0 <= k < trips.len() ==> 0 <= #[trigger] trips[k][1] < trips[k][2] <= 1000,
                diff.len() == 1001,
                forall |s: int| 0 <= s <= 1000 ==> #[trigger] diff@[s] as int == Self::delta_prefix(trips@, trips.len() as int, s),
                0 <= stop <= 1001,
                current as int
                    == if stop == 0 {
                        0
                    } else {
                        Self::load_prefix(trips@, trips.len() as int, stop as int - 1)
                    },
                forall |k: int| 0 <= k < stop ==> Self::load_prefix(trips@, trips.len() as int, k) <= capacity as int,
            decreases 1001 - stop,
        {
            proof {
                let s = stop as int;
                if stop > 0 {
                    Self::lemma_load_bound(trips@, trips.len() as int, s - 1);
                }
                Self::lemma_delta_bound(trips@, trips.len() as int, s);
                assert(diff@[s] as int == Self::delta_prefix(trips@, trips.len() as int, s));
                if stop == 0 {
                    assert(current as int == 0);
                } else {
                    assert(current as int == Self::load_prefix(trips@, trips.len() as int, s - 1));
                    assert(0 <= current as int <= 100 * trips.len() as int);
                }
                assert(-(100 * trips.len() as int) <= diff@[s] as int <= 100 * trips.len() as int);
                assert(trips.len() as int <= 1000);
                assert(-100_000 <= current as int + diff@[s] as int <= 200_000) by (nonlinear_arith)
                    requires
                        -100 * trips.len() as int <= diff@[s] as int <= 100 * trips.len() as int,
                        stop == 0 ==> current as int == 0,
                        stop > 0 ==> 0 <= current as int <= 100 * trips.len() as int,
                        trips.len() as int <= 1000
                {}
            }
            let ghost old_current = current as int;
            let next = current + diff[stop];
            current = next;

            proof {
                let s = stop as int;
                Self::lemma_load_step(trips@, trips.len() as int, s);
                assert(diff@[s] as int == Self::delta_prefix(trips@, trips.len() as int, s));
                assert(current == next);
                assert(next as int == old_current + diff@[s] as int);
                assert(current as int == old_current + diff@[s] as int);
                if stop == 0 {
                    assert(Self::load_prefix(trips@, trips.len() as int, s) == Self::delta_prefix(trips@, trips.len() as int, s));
                    assert(current as int == Self::load_prefix(trips@, trips.len() as int, s));
                } else {
                    assert(old_current == Self::load_prefix(trips@, trips.len() as int, s - 1));
                    assert(Self::load_prefix(trips@, trips.len() as int, s)
                        == Self::load_prefix(trips@, trips.len() as int, s - 1)
                            + Self::delta_prefix(trips@, trips.len() as int, s));
                    assert(current as int == Self::load_prefix(trips@, trips.len() as int, s));
                }
            }

            if current > capacity as i64 {
                proof {
                    let s = stop as int;
                    assert(Self::load_prefix(trips@, trips.len() as int, s) > capacity as int);
                    assert(!(forall |k: int| 0 <= k <= 1000 ==> #[trigger] Self::load_prefix(trips@, trips.len() as int, k) <= capacity as int)) by {
                        assert(0 <= s <= 1000);
                    };
                }
                return false;
            }

            proof {
                let s = stop as int;
                assert(Self::load_prefix(trips@, trips.len() as int, s) <= capacity as int);
                assert forall |k: int| 0 <= k < stop + 1 implies Self::load_prefix(trips@, trips.len() as int, k) <= capacity as int by {
                    if k < stop as int {
                    } else {
                        assert(k == s);
                    }
                };
            }

            stop += 1;
        }

        proof {
            assert(stop == 1001);
            assert forall |k: int| 0 <= k <= 1000 implies #[trigger] Self::load_prefix(trips@, trips.len() as int, k) <= capacity as int by {
                assert(k < stop);
            };
        }

        true
    }
}

}
