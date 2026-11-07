use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_spec(s: Seq<i32>, hi: int) -> int
        decreases hi
    {
        if hi <= 1 { s[0] as int }
        else {
            let rest = Self::min_spec(s, hi - 1);
            if (s[hi - 1] as int) < rest { s[hi - 1] as int } else { rest }
        }
    }

    pub open spec fn max_spec(s: Seq<i32>, hi: int) -> int
        decreases hi
    {
        if hi <= 1 { s[0] as int }
        else {
            let rest = Self::max_spec(s, hi - 1);
            if (s[hi - 1] as int) > rest { s[hi - 1] as int } else { rest }
        }
    }

    pub open spec fn divides(d: int, n: int) -> bool
        recommends d > 0
    {
        n % d == 0
    }

    
    pub open spec fn gcd_rec(a: int, b: int) -> int
        decreases b
    {
        if b <= 0 { a }
        else { Self::gcd_rec(b, a % b) }
    }

    proof fn lemma_gcd_rec_positive(a: int, b: int)
        requires a >= 1, b >= 0,
        ensures Self::gcd_rec(a, b) >= 1,
        decreases b
    {
        if b > 0 {
            Self::lemma_gcd_rec_positive(b, a % b);
        }
    }

    proof fn lemma_gcd_rec_divides(a: int, b: int)
        requires a >= 1, b >= 0,
        ensures
            Self::divides(Self::gcd_rec(a, b), a),
            Self::divides(Self::gcd_rec(a, b), b),
        decreases b
    {
        if b <= 0 {
            assert(a % a == 0) by (nonlinear_arith) requires a >= 1;
            assert(0int % a == 0) by (nonlinear_arith) requires a >= 1;
        } else {
            Self::lemma_gcd_rec_divides(b, a % b);
            Self::lemma_gcd_rec_positive(b, a % b);
            let g = Self::gcd_rec(a, b);
            assert(b % g == 0);
            assert((a % b) % g == 0);
            
            
            let qb = b / g;
            let qr = (a % b) / g;
            let q = a / b;
            assert(b == g * qb) by (nonlinear_arith)
                requires g >= 1, b % g == 0, qb == b / g;
            assert(a % b == g * qr) by (nonlinear_arith)
                requires g >= 1, (a % b) % g == 0, qr == (a % b) / g;
            assert(a == q * b + a % b) by (nonlinear_arith)
                requires b >= 1, q == a / b;
            assert(a == g * (q * qb + qr)) by (nonlinear_arith)
                requires a == q * b + a % b, b == g * qb, a % b == g * qr;
            assert(a % g == 0) by (nonlinear_arith)
                requires g >= 1, a == g * (q * qb + qr);
        }
    }

    proof fn lemma_gcd_rec_greatest(a: int, b: int, d: int)
        requires a >= 1, b >= 0, d >= 1, Self::divides(d, a), Self::divides(d, b),
        ensures d <= Self::gcd_rec(a, b),
        decreases b
    {
        if b <= 0 {
            assert(a % d == 0);
            let qa = a / d;
            assert(a == d * qa) by (nonlinear_arith)
                requires d >= 1, a % d == 0, qa == a / d;
            assert(d <= a) by (nonlinear_arith)
                requires d >= 1, a >= 1, a == d * qa;
        } else {
            assert(a % d == 0);
            assert(b % d == 0);
            let qa = a / d;
            let qb = b / d;
            let q = a / b;
            assert(a == d * qa) by (nonlinear_arith)
                requires d >= 1, a % d == 0, qa == a / d;
            assert(b == d * qb) by (nonlinear_arith)
                requires d >= 1, b % d == 0, qb == b / d;
            assert(a == q * b + a % b) by (nonlinear_arith)
                requires b >= 1, q == a / b;
            assert(a % b == d * (qa - q * qb)) by (nonlinear_arith)
                requires a == q * b + a % b, a == d * qa, b == d * qb;
            assert((a % b) % d == 0) by (nonlinear_arith)
                requires d >= 1, a % b == d * (qa - q * qb);
            assert(Self::divides(d, a % b));
            Self::lemma_gcd_rec_greatest(b, a % b, d);
        }
    }

    pub fn find_gcd(nums: Vec<i32>) -> (res: i32)
        requires
            2 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            res >= 1,
            Self::divides(res as int, Self::min_spec(nums@, nums.len() as int)),
            Self::divides(res as int, Self::max_spec(nums@, nums.len() as int)),
            forall |d: int| 1 <= d <= 1000
                && Self::divides(d, Self::min_spec(nums@, nums.len() as int))
                && Self::divides(d, Self::max_spec(nums@, nums.len() as int))
                ==> d <= res as int,
    {
        let n = nums.len();
        let ghost s = nums@;
        let ghost n_int = n as int;

        let mut min_v = nums[0];
        let mut max_v = nums[0];
        let mut i: usize = 1;

        while i < n
            invariant
                1 <= i <= n,
                n == nums.len(),
                s == nums@,
                n_int == n as int,
                2 <= n <= 1000,
                forall |j: int| 0 <= j < n_int ==> 1 <= #[trigger] s[j] <= 1000,
                min_v as int == Self::min_spec(s, i as int),
                max_v as int == Self::max_spec(s, i as int),
                1 <= min_v <= 1000,
                1 <= max_v <= 1000,
            decreases n - i
        {
            if nums[i] < min_v {
                min_v = nums[i];
            }
            if nums[i] > max_v {
                max_v = nums[i];
            }
            i += 1;
        }

        let ghost the_min = min_v as int;
        let ghost the_max = max_v as int;

        proof {
            Self::lemma_gcd_rec_positive(max_v as int, min_v as int);
        }

        let mut a = max_v;
        let mut b = min_v;

        while b > 0
            invariant
                Self::gcd_rec(a as int, b as int) == Self::gcd_rec(the_max, the_min),
                a >= 1,
                b >= 0,
                a <= 1000,
                b <= 1000,
                the_min == min_v as int,
                the_max == max_v as int,
            decreases b as int
        {
            let temp = b;
            b = a % b;
            a = temp;
        }

        
        proof {
            
            assert(a as int == Self::gcd_rec(the_max, the_min));
            Self::lemma_gcd_rec_divides(the_max, the_min);
            Self::lemma_gcd_rec_positive(the_max, the_min);

            
            assert(Self::divides(a as int, the_max));
            assert(Self::divides(a as int, the_min));

            
            assert forall |d: int| d >= 1
                && Self::divides(d, the_min)
                && Self::divides(d, the_max)
                implies d <= a as int by {
                Self::lemma_gcd_rec_greatest(the_max, the_min, d);
            };
        }

        a
    }
}

}
