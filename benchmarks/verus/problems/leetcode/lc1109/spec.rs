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
    }
}

}
