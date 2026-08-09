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
        let zu: usize = zero as usize;
        let ou: usize = one as usize;
        let limu: usize = limit as usize;
        let md: i64 = 1000000007;

        let mut ways0: Vec<Vec<i64>> = Vec::new();
        let mut ways1: Vec<Vec<i64>> = Vec::new();

        let mut z: usize = 0;
        while z <= zu {
            let mut row0: Vec<i64> = Vec::new();
            let mut row1: Vec<i64> = Vec::new();
            let mut o: usize = 0;
            while o <= ou {
                if z == 0 && o == 0 {
                    row0.push(1);
                    row1.push(1);
                } else {
                    let upto0: usize = if z <= limu { z } else { limu };
                    let mut s0: i64 = 0;
                    let mut u: usize = 1;
                    while u <= upto0 {
                        let idx0: usize = z - u;
                        let term_val: i64 = ways1[idx0][o];
                        s0 = (s0 + term_val) % md;
                        u += 1;
                    }
                    row0.push(s0);

                    let upto1: usize = if o <= limu { o } else { limu };
                    let mut s1: i64 = 0;
                    let mut u2: usize = 1;
                    while u2 <= upto1 {
                        let idx1: usize = o - u2;
                        let term_val1: i64 = row0[idx1];
                        s1 = (s1 + term_val1) % md;
                        u2 += 1;
                    }
                    row1.push(s1);
                }
                o += 1;
            }
            ways0.push(row0);
            ways1.push(row1);
            z += 1;
        }

        let a = ways0[zu][ou];
        let b = ways1[zu][ou];
        let result = ((a + b) % md) as i32;
        result
    }
}

}
