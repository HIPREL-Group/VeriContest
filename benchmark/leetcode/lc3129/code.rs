impl Solution {
    const MOD_I64: i64 = 1000000007;

    fn sum_zero_exec(z: i32, o: i32, limit: i32, upto: i32) -> i64 {
        if upto <= 0 {
            0
        } else {
            let prev = Self::sum_zero_exec(z, o, limit, upto - 1);
            let w = Self::ways_exec(z - upto, o, limit, false);
            (prev + w) % Self::MOD_I64
        }
    }

    fn sum_one_exec(z: i32, o: i32, limit: i32, upto: i32) -> i64 {
        if upto <= 0 {
            0
        } else {
            let prev = Self::sum_one_exec(z, o, limit, upto - 1);
            let w = Self::ways_exec(z, o - upto, limit, true);
            (prev + w) % Self::MOD_I64
        }
    }

    fn ways_exec(z: i32, o: i32, limit: i32, first_zero: bool) -> i64 {
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

    pub fn number_of_stable_arrays(zero: i32, one: i32, limit: i32) -> i32 {
        let a = Self::ways_exec(zero, one, limit, true);
        let b = Self::ways_exec(zero, one, limit, false);
        ((a + b) % Self::MOD_I64) as i32
    }
}
