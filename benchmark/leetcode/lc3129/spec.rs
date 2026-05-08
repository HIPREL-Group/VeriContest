use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn MOD() -> int { 1000000007 }

    pub open spec fn sum_zero_prefix(z: int, o: int, limit: int, upto: int) -> int
        recommends
            0 <= z,
            0 <= o,
            1 <= limit,
            0 <= upto <= z,
        decreases z + o, 0int, upto when z >= 0 && o >= 0 && 0 <= upto <= z
    {
        if upto <= 0 {
            0
        } else {
            (Self::sum_zero_prefix(z, o, limit, upto - 1) + Self::ways(z - upto, o, limit, false))
                % Self::MOD()
        }
    }

    pub open spec fn sum_one_prefix(z: int, o: int, limit: int, upto: int) -> int
        recommends
            0 <= z,
            0 <= o,
            1 <= limit,
            0 <= upto <= o,
        decreases z + o, 0int, upto when z >= 0 && o >= 0 && 0 <= upto <= o
    {
        if upto <= 0 {
            0
        } else {
            (Self::sum_one_prefix(z, o, limit, upto - 1) + Self::ways(z, o - upto, limit, true))
                % Self::MOD()
        }
    }

    pub open spec fn ways(z: int, o: int, limit: int, first_zero: bool) -> int
        recommends
            0 <= z,
            0 <= o,
            1 <= limit,
        decreases z + o, 1int when z >= 0 && o >= 0
    {
        if z == 0 && o == 0 {
            1
        } else if first_zero {
            Self::sum_zero_prefix(z, o, limit, if z <= limit { z } else { limit })
        } else {
            Self::sum_one_prefix(z, o, limit, if o <= limit { o } else { limit })
        }
    }

    pub open spec fn stable_arrays_mod(z: int, o: int, limit: int) -> int
        recommends
            0 <= z,
            0 <= o,
            1 <= limit,
    {
        (Self::ways(z, o, limit, true) + Self::ways(z, o, limit, false)) % Self::MOD()
    }

    pub fn number_of_stable_arrays(zero: i32, one: i32, limit: i32) -> (result: i32)
        requires
            1 <= zero <= 200,
            1 <= one <= 200,
            1 <= limit <= 200,
        ensures
            result as int == Self::stable_arrays_mod(zero as int, one as int, limit as int),
    {
    }
}

}
