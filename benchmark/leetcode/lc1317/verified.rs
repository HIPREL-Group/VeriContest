use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_no_zero(x: int) -> bool
        decreases x,
    {
        if x <= 0 {
            false
        } else if x < 10 {
            true
        } else {
            x % 10 != 0 && Solution::is_no_zero(x / 10)
        }
    }

    proof fn existence_lemma(n: int)
        requires
            2 <= n <= 10000,
        ensures
            exists|a: int| 1 <= a < n && #[trigger] Solution::is_no_zero(a) && Solution::is_no_zero(n - a),
    {
        reveal_with_fuel(Solution::is_no_zero, 5);
        if Solution::is_no_zero(n - 1) {
            assert(Solution::is_no_zero(1int));
        } else if n >= 3 && Solution::is_no_zero(n - 2) {
            assert(Solution::is_no_zero(2int));
        } else if n >= 4 && Solution::is_no_zero(n - 3) {
            assert(Solution::is_no_zero(3int));
        } else if n >= 5 && Solution::is_no_zero(n - 4) {
            assert(Solution::is_no_zero(4int));
        } else if n >= 6 && Solution::is_no_zero(n - 5) {
            assert(Solution::is_no_zero(5int));
        } else if n >= 7 && Solution::is_no_zero(n - 6) {
            assert(Solution::is_no_zero(6int));
        } else if n >= 8 && Solution::is_no_zero(n - 7) {
            assert(Solution::is_no_zero(7int));
        } else if n >= 9 && Solution::is_no_zero(n - 8) {
            assert(Solution::is_no_zero(8int));
        } else if n >= 10 && Solution::is_no_zero(n - 9) {
            assert(Solution::is_no_zero(9int));
        } else if n >= 12 && Solution::is_no_zero(n - 11) {
            assert(Solution::is_no_zero(11int));
        } else if n >= 13 && Solution::is_no_zero(n - 12) {
            assert(Solution::is_no_zero(12int));
        } else if n >= 14 && Solution::is_no_zero(n - 13) {
            assert(Solution::is_no_zero(13int));
        } else if n >= 15 && Solution::is_no_zero(n - 14) {
            assert(Solution::is_no_zero(14int));
        } else if n >= 16 && Solution::is_no_zero(n - 15) {
            assert(Solution::is_no_zero(15int));
        } else if n >= 17 && Solution::is_no_zero(n - 16) {
            assert(Solution::is_no_zero(16int));
        } else if n >= 18 && Solution::is_no_zero(n - 17) {
            assert(Solution::is_no_zero(17int));
        } else if n >= 19 && Solution::is_no_zero(n - 18) {
            assert(Solution::is_no_zero(18int));
        } else if n >= 20 && Solution::is_no_zero(n - 19) {
            assert(Solution::is_no_zero(19int));
        } else if n >= 22 && Solution::is_no_zero(n - 21) {
            assert(Solution::is_no_zero(21int));
        } else if n >= 23 && Solution::is_no_zero(n - 22) {
            assert(Solution::is_no_zero(22int));
        } else if n >= 112 && Solution::is_no_zero(n - 111) {
            assert(Solution::is_no_zero(111int));
        } else if n >= 113 && Solution::is_no_zero(n - 112) {
            assert(Solution::is_no_zero(112int));
        } else {
            assert(false);
        }
    }

    fn check_no_zero(x: i32) -> (result: bool)
        requires
            0 <= x <= 10000,
        ensures
            result == Solution::is_no_zero(x as int),
    {
        if x <= 0 {
            return false;
        }
        let mut val = x;
        while val >= 10
            invariant
                1 <= val <= x,
                Solution::is_no_zero(x as int) == Solution::is_no_zero(val as int),
            decreases val,
        {
            if val % 10 == 0 {
                return false;
            }
            val = val / 10;
        }
        true
    }

    pub fn get_no_zero_integers(n: i32) -> (result: Vec<i32>)
        requires
            2 <= n <= 10000,
        ensures
            result@.len() == 2,
            1 <= result@[0] && 1 <= result@[1],
            result@[0] + result@[1] == n,
            Solution::is_no_zero(result@[0] as int),
            Solution::is_no_zero(result@[1] as int),
    {
        let mut a: i32 = 1;
        while a < n
            invariant
                1 <= a <= n,
                2 <= n <= 10000,
                forall|j: int| 1 <= j < a as int ==>
                    !(#[trigger] Solution::is_no_zero(j) && Solution::is_no_zero(n as int - j)),
            decreases n - a,
        {
            let b = n - a;
            if Self::check_no_zero(a) && Self::check_no_zero(b) {
                let mut res = Vec::new();
                res.push(a);
                res.push(b);
                return res;
            }
            a = a + 1;
        }
        proof {
            Self::existence_lemma(n as int);
            assert(false);
        }
        let mut res = Vec::new();
        res.push(1);
        res.push(n - 1);
        res
    }
}

} 
