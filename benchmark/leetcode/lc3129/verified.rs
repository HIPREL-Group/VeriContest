use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn MOD() -> int { 1000000007 }
    const MOD_I64: i64 = 1000000007;

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

    fn sum_zero_exec(z: i32, o: i32, limit: i32, upto: i32) -> (result: i64)
        requires
            0 <= z <= 200,
            0 <= o <= 200,
            1 <= limit <= 200,
            0 <= upto <= z,
        ensures
            result as int == Self::sum_zero_prefix(z as int, o as int, limit as int, upto as int),
            0 <= result < Self::MOD_I64,
        decreases (z as int + o as int), 0int, (upto as int),
    {
        if upto <= 0 {
            0
        } else {
            let prev = Self::sum_zero_exec(z, o, limit, upto - 1);
            let w = Self::ways_exec(z - upto, o, limit, false);
            (prev + w) % Self::MOD_I64
        }
    }

    fn sum_one_exec(z: i32, o: i32, limit: i32, upto: i32) -> (result: i64)
        requires
            0 <= z <= 200,
            0 <= o <= 200,
            1 <= limit <= 200,
            0 <= upto <= o,
        ensures
            result as int == Self::sum_one_prefix(z as int, o as int, limit as int, upto as int),
            0 <= result < Self::MOD_I64,
        decreases (z as int + o as int), 0int, (upto as int),
    {
        if upto <= 0 {
            0
        } else {
            let prev = Self::sum_one_exec(z, o, limit, upto - 1);
            let w = Self::ways_exec(z, o - upto, limit, true);
            (prev + w) % Self::MOD_I64
        }
    }

    fn ways_exec(z: i32, o: i32, limit: i32, first_zero: bool) -> (result: i64)
        requires
            0 <= z <= 200,
            0 <= o <= 200,
            1 <= limit <= 200,
        ensures
            result as int == Self::ways(z as int, o as int, limit as int, first_zero),
            0 <= result < Self::MOD_I64,
        decreases (z as int + o as int), 1int, 0int,
    {
        if z == 0 && o == 0 {
            1
        } else if first_zero {
            let upto = if z <= limit { z } else { limit };
            Self::sum_zero_exec(z, o, limit, upto)
        } else {
            let upto = if o <= limit { o } else { limit };
            Self::sum_one_exec(z, o, limit, upto)
        }
    }

    pub fn number_of_stable_arrays(zero: i32, one: i32, limit: i32) -> (result: i32)
        requires
            1 <= zero <= 200,
            1 <= one <= 200,
            1 <= limit <= 200,
        ensures
            result as int == Self::stable_arrays_mod(zero as int, one as int, limit as int),
    {
        let a = Self::ways_exec(zero, one, limit, true);
        let b = Self::ways_exec(zero, one, limit, false);
        ((a + b) % Self::MOD_I64) as i32
    }
}

}
