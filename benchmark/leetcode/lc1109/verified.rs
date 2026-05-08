use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn booking_seats_at(booking: Vec<i32>, flight: int) -> int
        recommends
            booking@.len() == 3,
    {
        if booking@[0] as int - 1 <= flight && flight <= booking@[1] as int - 1 {
            booking@[2] as int
        } else {
            0
        }
    }

    pub open spec fn total_seats(bookings: Seq<Vec<i32>>, count: int, flight: int) -> int
        recommends
            0 <= count <= bookings.len(),
            forall |i: int| 0 <= i < bookings.len() ==> #[trigger] bookings[i]@.len() == 3,
        decreases count,
    {
        if count <= 0 {
            0
        } else {
            Self::total_seats(bookings, count - 1, flight) + Self::booking_seats_at(bookings[count - 1], flight)
        }
    }

    pub open spec fn booking_delta_at(booking: Vec<i32>, flight: int) -> int
        recommends
            booking@.len() == 3,
    {
        (if booking@[0] as int - 1 == flight { booking@[2] as int } else { 0 })
            - (if booking@[1] as int == flight { booking@[2] as int } else { 0 })
    }

    pub open spec fn delta_prefix(bookings: Seq<Vec<i32>>, count: int, flight: int) -> int
        recommends
            0 <= count <= bookings.len(),
            forall |i: int| 0 <= i < bookings.len() ==> #[trigger] bookings[i]@.len() == 3,
        decreases count,
    {
        if count <= 0 {
            0
        } else {
            Self::delta_prefix(bookings, count - 1, flight) + Self::booking_delta_at(bookings[count - 1], flight)
        }
    }

    proof fn lemma_seats_step(bookings: Seq<Vec<i32>>, count: int, flight: int)
        requires
            0 <= count <= bookings.len(),
            0 <= flight,
            forall |i: int| 0 <= i < bookings.len() ==> #[trigger] bookings[i]@.len() == 3,
            forall |i: int| 0 <= i < bookings.len() ==> 1 <= #[trigger] bookings[i]@[0] <= bookings[i]@[1],
            forall |i: int| 0 <= i < bookings.len() ==> 1 <= #[trigger] bookings[i]@[2] <= 10_000,
        ensures
            flight == 0 ==> Self::total_seats(bookings, count, flight) == Self::delta_prefix(bookings, count, flight),
            flight > 0 ==> Self::total_seats(bookings, count, flight)
                == Self::total_seats(bookings, count, flight - 1) + Self::delta_prefix(bookings, count, flight),
        decreases count,
    {
        if count > 0 {
            Self::lemma_seats_step(bookings, count - 1, flight);
            let booking = bookings[count - 1];
            let first = booking@[0] as int;
            let last = booking@[1] as int;
            let seats = booking@[2] as int;

            assert(Self::total_seats(bookings, count, flight)
                == Self::total_seats(bookings, count - 1, flight) + Self::booking_seats_at(booking, flight));
            assert(Self::delta_prefix(bookings, count, flight)
                == Self::delta_prefix(bookings, count - 1, flight) + Self::booking_delta_at(booking, flight));

            if flight == 0 {
                if first - 1 == 0 {
                    assert(Self::booking_seats_at(booking, flight) == seats);
                    assert(Self::booking_delta_at(booking, flight) == seats);
                } else {
                    assert(Self::booking_seats_at(booking, flight) == 0);
                    assert(Self::booking_delta_at(booking, flight) == 0);
                }
            } else {
                if flight < first - 1 {
                    assert(Self::booking_seats_at(booking, flight - 1) == 0);
                    assert(Self::booking_seats_at(booking, flight) == 0);
                    assert(Self::booking_delta_at(booking, flight) == 0);
                } else if flight == first - 1 {
                    assert(Self::booking_seats_at(booking, flight - 1) == 0);
                    assert(Self::booking_seats_at(booking, flight) == seats);
                    assert(Self::booking_delta_at(booking, flight) == seats);
                } else if flight < last {
                    assert(Self::booking_seats_at(booking, flight - 1) == seats);
                    assert(Self::booking_seats_at(booking, flight) == seats);
                    assert(Self::booking_delta_at(booking, flight) == 0);
                } else if flight == last {
                    assert(Self::booking_seats_at(booking, flight - 1) == seats);
                    assert(Self::booking_seats_at(booking, flight) == 0);
                    assert(Self::booking_delta_at(booking, flight) == -seats);
                } else {
                    assert(Self::booking_seats_at(booking, flight - 1) == 0);
                    assert(Self::booking_seats_at(booking, flight) == 0);
                    assert(Self::booking_delta_at(booking, flight) == 0);
                }
            }
        }
    }

    proof fn lemma_delta_bound(bookings: Seq<Vec<i32>>, count: int, flight: int)
        requires
            0 <= count <= bookings.len(),
            forall |i: int| 0 <= i < bookings.len() ==> #[trigger] bookings[i]@.len() == 3,
            forall |i: int| 0 <= i < bookings.len() ==> 1 <= #[trigger] bookings[i]@[2] <= 10_000,
        ensures
            -(10_000 * count) <= Self::delta_prefix(bookings, count, flight) <= 10_000 * count,
        decreases count,
    {
        if count > 0 {
            Self::lemma_delta_bound(bookings, count - 1, flight);
            let booking = bookings[count - 1];
            let seats = booking@[2] as int;
            assert(Self::delta_prefix(bookings, count, flight)
                == Self::delta_prefix(bookings, count - 1, flight) + Self::booking_delta_at(booking, flight));
            if booking@[0] as int - 1 == flight {
                if booking@[1] as int == flight {
                    assert(Self::booking_delta_at(booking, flight) == 0);
                } else {
                    assert(Self::booking_delta_at(booking, flight) == seats);
                }
            } else if booking@[1] as int == flight {
                assert(Self::booking_delta_at(booking, flight) == -seats);
            } else {
                assert(Self::booking_delta_at(booking, flight) == 0);
            }
        }
    }

    proof fn lemma_seats_bound(bookings: Seq<Vec<i32>>, count: int, flight: int)
        requires
            0 <= count <= bookings.len(),
            forall |i: int| 0 <= i < bookings.len() ==> #[trigger] bookings[i]@.len() == 3,
            forall |i: int| 0 <= i < bookings.len() ==> 1 <= #[trigger] bookings[i]@[2] <= 10_000,
        ensures
            0 <= Self::total_seats(bookings, count, flight) <= 10_000 * count,
        decreases count,
    {
        if count > 0 {
            Self::lemma_seats_bound(bookings, count - 1, flight);
            let booking = bookings[count - 1];
            let seats = booking@[2] as int;
            assert(Self::total_seats(bookings, count, flight)
                == Self::total_seats(bookings, count - 1, flight) + Self::booking_seats_at(booking, flight));
            if booking@[0] as int - 1 <= flight && flight <= booking@[1] as int - 1 {
                assert(Self::booking_seats_at(booking, flight) == seats);
            } else {
                assert(Self::booking_seats_at(booking, flight) == 0);
            }
        }
    }

    pub fn corp_flight_bookings(bookings: Vec<Vec<i32>>, n: i32) -> (result: Vec<i32>)
        requires
            1 <= n <= 20_000,
            1 <= bookings.len() <= 20_000,
            forall |i: int| 0 <= i < bookings.len() ==> #[trigger] bookings[i]@.len() == 3,
            forall |i: int| 0 <= i < bookings.len() ==> 1 <= #[trigger] bookings[i][0] <= bookings[i][1] <= n,
            forall |i: int| 0 <= i < bookings.len() ==> 1 <= #[trigger] bookings[i][2] <= 10_000,
        ensures
            result@.len() == n as int,
            forall |f: int| 0 <= f < n as int ==> #[trigger] result@[f] as int == Self::total_seats(bookings@, bookings.len() as int, f),
    {
        let nn = n as usize;
        let mut diff: Vec<i64> = Vec::new();
        let mut fill = 0usize;

        while fill <= nn
            invariant
                0 <= fill <= nn + 1,
                diff.len() == fill,
                forall |k: int| 0 <= k < fill ==> #[trigger] diff@[k] == 0,
                nn == n as usize,
                1 <= n <= 20_000,
                1 <= nn <= 20_000,
            decreases nn + 1 - fill,
        {
            diff.push(0);
            fill += 1;
        }

        let mut i = 0usize;
        while i < bookings.len()
            invariant
                1 <= n <= 20_000,
                nn == n as usize,
                1 <= bookings.len() <= 20_000,
                forall |k: int| 0 <= k < bookings.len() ==> #[trigger] bookings[k]@.len() == 3,
                forall |k: int| 0 <= k < bookings.len() ==> 1 <= #[trigger] bookings[k][0] <= bookings[k][1] <= n,
                forall |k: int| 0 <= k < bookings.len() ==> 1 <= #[trigger] bookings[k][2] <= 10_000,
                0 <= i <= bookings.len(),
                diff.len() == nn + 1,
                forall |f: int| 0 <= f <= nn as int ==> #[trigger] diff@[f] as int == Self::delta_prefix(bookings@, i as int, f),
            decreases bookings.len() - i,
        {
            proof {
                assert(bookings[i as int]@.len() == 3);
                assert(1 <= bookings[i as int][0] <= bookings[i as int][1] <= n);
            }

            let first = bookings[i][0] as usize;
            let last = bookings[i][1] as usize;
            let seats = bookings[i][2] as i64;

            proof {
                let idx = i as int;
                Self::lemma_delta_bound(bookings@, idx, (first - 1) as int);
                Self::lemma_delta_bound(bookings@, idx, last as int);
                assert(diff@[(first - 1) as int] as int == Self::delta_prefix(bookings@, idx, (first - 1) as int));
                assert(diff@[last as int] as int == Self::delta_prefix(bookings@, idx, last as int));
                assert(-(10_000 * idx) <= diff@[(first - 1) as int] as int <= 10_000 * idx);
                assert(-(10_000 * idx) <= diff@[last as int] as int <= 10_000 * idx);
                assert(1 <= seats as int <= 10_000);
                assert(-200_010_000 <= diff@[(first - 1) as int] as int + seats as int <= 200_010_000) by (nonlinear_arith)
                    requires
                        -(10_000 * idx) <= diff@[(first - 1) as int] as int <= 10_000 * idx,
                        1 <= seats as int <= 10_000,
                        idx <= 20_000
                {}
                assert(-200_010_000 <= diff@[last as int] as int - seats as int <= 200_010_000) by (nonlinear_arith)
                    requires
                        -(10_000 * idx) <= diff@[last as int] as int <= 10_000 * idx,
                        1 <= seats as int <= 10_000,
                        idx <= 20_000
                {}
            }

            let add_value = diff[first - 1] + seats;
            let sub_value = diff[last] - seats;
            let ghost before = diff@;

            diff.set(first - 1, add_value);
            let ghost after_add = diff@;
            diff.set(last, sub_value);

            proof {
                let idx = i as int;
                let first_idx = (first - 1) as int;
                let last_idx = last as int;
                assert(0 <= first_idx <= nn as int);
                assert(0 <= last_idx <= nn as int);
                assert(first_idx < last_idx);
                assert(after_add == before.update(first_idx, add_value));
                assert(diff@ == after_add.update(last_idx, sub_value));

                assert forall |f: int| 0 <= f <= nn as int implies #[trigger] diff@[f] as int == Self::delta_prefix(bookings@, idx + 1, f) by {
                    assert(Self::delta_prefix(bookings@, idx + 1, f)
                        == Self::delta_prefix(bookings@, idx, f) + Self::booking_delta_at(bookings[idx], f));
                    if f == first_idx {
                        assert(last_idx != f);
                        assert(after_add[f] == before[f] + seats);
                        assert(diff@[f] == after_add[f]);
                        assert(Self::booking_delta_at(bookings[idx], f) == bookings[idx]@[2] as int);
                    } else if f == last_idx {
                        assert(first_idx != f);
                        assert(after_add[f] == before[f]);
                        assert(diff@[f] == after_add[f] - seats);
                        assert(Self::booking_delta_at(bookings[idx], f) == -(bookings[idx]@[2] as int));
                    } else {
                        assert(after_add[f] == before[f]);
                        assert(diff@[f] == after_add[f]);
                        assert(Self::booking_delta_at(bookings[idx], f) == 0);
                    }
                };
            }

            i += 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut current = 0i64;
        let mut f = 0usize;
        while f < nn
            invariant
                1 <= n <= 20_000,
                nn == n as usize,
                1 <= bookings.len() <= 20_000,
                forall |k: int| 0 <= k < bookings.len() ==> #[trigger] bookings[k]@.len() == 3,
                forall |k: int| 0 <= k < bookings.len() ==> 1 <= #[trigger] bookings[k][0] <= bookings[k][1] <= n,
                forall |k: int| 0 <= k < bookings.len() ==> 1 <= #[trigger] bookings[k][2] <= 10_000,
                diff.len() == nn + 1,
                forall |s: int| 0 <= s <= nn as int ==> #[trigger] diff@[s] as int == Self::delta_prefix(bookings@, bookings.len() as int, s),
                0 <= f <= nn,
                result@.len() == f as int,
                current as int
                    == if f == 0 {
                        0
                    } else {
                        Self::total_seats(bookings@, bookings.len() as int, f as int - 1)
                    },
                forall |k: int| 0 <= k < f as int ==> #[trigger] result@[k] as int == Self::total_seats(bookings@, bookings.len() as int, k),
            decreases nn - f,
        {
            proof {
                let fl = f as int;
                if f > 0 {
                    Self::lemma_seats_bound(bookings@, bookings.len() as int, fl - 1);
                }
                Self::lemma_delta_bound(bookings@, bookings.len() as int, fl);
                assert(diff@[fl] as int == Self::delta_prefix(bookings@, bookings.len() as int, fl));
                if f == 0 {
                    assert(current as int == 0);
                } else {
                    assert(current as int == Self::total_seats(bookings@, bookings.len() as int, fl - 1));
                    assert(0 <= current as int <= 10_000 * bookings.len() as int);
                }
                assert(-(10_000 * bookings.len() as int) <= diff@[fl] as int <= 10_000 * bookings.len() as int);
                assert(bookings.len() as int <= 20_000);
                assert(-200_000_000 <= current as int + diff@[fl] as int <= 400_000_000) by (nonlinear_arith)
                    requires
                        -(10_000 * bookings.len() as int) <= diff@[fl] as int <= 10_000 * bookings.len() as int,
                        f == 0 ==> current as int == 0,
                        f > 0 ==> 0 <= current as int <= 10_000 * bookings.len() as int,
                        bookings.len() as int <= 20_000
                {}
            }

            let ghost old_current = current as int;
            let next = current + diff[f];
            current = next;

            proof {
                let fl = f as int;
                Self::lemma_seats_step(bookings@, bookings.len() as int, fl);
                assert(diff@[fl] as int == Self::delta_prefix(bookings@, bookings.len() as int, fl));
                assert(current as int == old_current + diff@[fl] as int);
                if f == 0 {
                    assert(Self::total_seats(bookings@, bookings.len() as int, fl) == Self::delta_prefix(bookings@, bookings.len() as int, fl));
                    assert(current as int == Self::total_seats(bookings@, bookings.len() as int, fl));
                } else {
                    assert(old_current == Self::total_seats(bookings@, bookings.len() as int, fl - 1));
                    assert(Self::total_seats(bookings@, bookings.len() as int, fl)
                        == Self::total_seats(bookings@, bookings.len() as int, fl - 1)
                            + Self::delta_prefix(bookings@, bookings.len() as int, fl));
                    assert(current as int == Self::total_seats(bookings@, bookings.len() as int, fl));
                }
                Self::lemma_seats_bound(bookings@, bookings.len() as int, fl);
                assert(0 <= current as int <= 10_000 * bookings.len() as int);
                assert(0 <= current as int <= 200_000_000) by (nonlinear_arith)
                    requires
                        0 <= current as int <= 10_000 * bookings.len() as int,
                        bookings.len() as int <= 20_000
                {}
            }

            result.push(current as i32);

            proof {
                let fl = f as int;
                assert(result@.len() == fl + 1);
                assert(result@[fl] as int == current as int);
                assert(current as int == Self::total_seats(bookings@, bookings.len() as int, fl));
                assert forall |k: int| 0 <= k < fl + 1 implies #[trigger] result@[k] as int == Self::total_seats(bookings@, bookings.len() as int, k) by {
                    if k < fl {
                    } else {
                        assert(k == fl);
                    }
                };
            }

            f += 1;
        }

        result
    }
}

}
