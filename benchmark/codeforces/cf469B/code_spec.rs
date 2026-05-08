use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_schedule(starts: Seq<i32>, ends: Seq<i32>) -> bool {
        1 <= starts.len() <= 50
            && starts.len() == ends.len()
            && forall|i: int| 0 <= i < starts.len() ==> 0 <= #[trigger] starts[i] < #[trigger] ends[i] <= 1000
    }

    pub open spec fn intervals_overlap_at_shift(
        z_starts: Seq<i32>,
        z_ends: Seq<i32>,
        x_starts: Seq<i32>,
        x_ends: Seq<i32>,
        i: int,
        j: int,
        t: int,
    ) -> bool
        recommends
            0 <= i < z_starts.len(),
            0 <= j < x_starts.len(),
            z_starts.len() == z_ends.len(),
            x_starts.len() == x_ends.len(),
    {
        x_starts[j] + t <= z_ends[i] && z_starts[i] <= x_ends[j] + t
    }

    pub open spec fn suitable_shift(
        z_starts: Seq<i32>,
        z_ends: Seq<i32>,
        x_starts: Seq<i32>,
        x_ends: Seq<i32>,
        t: int,
    ) -> bool
        recommends
            z_starts.len() == z_ends.len(),
            x_starts.len() == x_ends.len(),
    {
        exists|i: int, j: int|
            0 <= i < z_starts.len()
                && 0 <= j < x_starts.len()
                && #[trigger] Self::intervals_overlap_at_shift(z_starts, z_ends, x_starts, x_ends, i, j, t)
    }

    pub open spec fn count_suitable_shifts(
        z_starts: Seq<i32>,
        z_ends: Seq<i32>,
        x_starts: Seq<i32>,
        x_ends: Seq<i32>,
        l: int,
        upto: int,
    ) -> int
        recommends
            l <= upto,
            z_starts.len() == z_ends.len(),
            x_starts.len() == x_ends.len(),
        decreases upto - l,
    {
        if upto <= l {
            0
        } else {
            Self::count_suitable_shifts(z_starts, z_ends, x_starts, x_ends, l, upto - 1)
                + if Self::suitable_shift(z_starts, z_ends, x_starts, x_ends, upto - 1) {
                    1int
                } else {
                    0int
                }
        }
    }

    pub fn count_chat_times(
        z_starts: Vec<i32>,
        z_ends: Vec<i32>,
        x_starts: Vec<i32>,
        x_ends: Vec<i32>,
        l: i32,
        r: i32,
    ) -> (result: i32)
        requires
            Self::valid_schedule(z_starts@, z_ends@),
            Self::valid_schedule(x_starts@, x_ends@),
            0 <= l <= r <= 1000,
        ensures
            result as int == Self::count_suitable_shifts(z_starts@, z_ends@, x_starts@, x_ends@, l as int, r as int + 1),
    {
        let mut result = 0i32;
        let mut t = l;
        while t <= r {
            let mut found = false;
            let mut i = 0usize;
            while i < z_starts.len() && !found {
                let mut j = 0usize;
                while j < x_starts.len() && !found {
                    let zs = z_starts[i];
                    let ze = z_ends[i];
                    let xs = x_starts[j];
                    let xe = x_ends[j];
                    if xs + t <= ze && zs <= xe + t {
                        found = true;
                    } else {
                        j += 1;
                    }
                }
                if !found {
                    i += 1;
                }
            }
            if found {
                result += 1;
            }
            t += 1;
        }
        result
    }
}

}
