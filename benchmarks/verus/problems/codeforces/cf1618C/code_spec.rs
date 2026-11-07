use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_max_val() -> int {
        1000000000000000000
    }

    pub open spec fn spec_gcd_nat(a: nat, b: nat) -> nat
        decreases b,
    {
        if b == 0 {
            a
        } else {
            Self::spec_gcd_nat(b, a % b)
        }
    }

    pub open spec fn spec_gcd(a: int, b: int) -> int
        recommends
            0 <= a,
            0 <= b,
    {
        Self::spec_gcd_nat(a as nat, b as nat) as int
    }

    pub open spec fn spec_even_gcd_prefix(a: Seq<i64>, hi: int) -> int
        recommends
            hi % 2 == 0,
            2 <= hi <= a.len() + 1,
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
        decreases hi,
    {
        if hi <= 2 {
            a[0] as int
        } else {
            Self::spec_gcd(Self::spec_even_gcd_prefix(a, hi - 2), a[hi - 2] as int)
        }
    }

    pub open spec fn spec_odd_gcd_prefix(a: Seq<i64>, hi: int) -> int
        recommends
            hi % 2 == 1,
            3 <= hi <= a.len() + 1,
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
        decreases hi,
    {
        if hi <= 3 {
            a[1] as int
        } else {
            Self::spec_gcd(Self::spec_odd_gcd_prefix(a, hi - 2), a[hi - 2] as int)
        }
    }

    pub open spec fn spec_gcd_all_even(a: Seq<i64>) -> int
        recommends
            2 <= a.len() <= 100,
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
    {
        let n = a.len() as int;
        Self::spec_even_gcd_prefix(a, n + n % 2)
    }

    pub open spec fn spec_gcd_all_odd(a: Seq<i64>) -> int
        recommends
            2 <= a.len() <= 100,
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
    {
        let n = a.len() as int;
        Self::spec_odd_gcd_prefix(a, n + 1 - n % 2)
    }

    pub open spec fn spec_divisible_by(x: int, d: int) -> bool {
        d > 0 && x % d == 0
    }

    pub open spec fn spec_beautiful(seq: Seq<i64>, d: int) -> bool {
        forall|i: int|
            #![trigger seq[i]]
            0 <= i < seq.len() - 1 ==> Self::spec_divisible_by(seq[i] as int, d)
                != Self::spec_divisible_by(seq[i + 1] as int, d)
    }

    pub open spec fn spec_exists_beautiful_d(seq: Seq<i64>) -> bool {
        exists|d: int|
            #![trigger Self::spec_beautiful(seq, d)]
            1 <= d <= Self::spec_max_val() && Self::spec_beautiful(seq, d)
    }

    pub fn gcd_two(x: i64, y: i64) -> (g: i64)
        requires
            1 <= x <= Self::spec_max_val(),
            1 <= y <= Self::spec_max_val(),
        ensures
            1 <= g <= Self::spec_max_val(),
            g as int == Self::spec_gcd(x as int, y as int),
    {
        let mut x = x;
        let mut y = y;
        while y != 0 {
            let t = x % y;
            x = y;
            y = t;
        }
        x
    }

    pub fn paint_the_array(a: Vec<i64>) -> (r: i64)
        requires
            2 <= a.len() <= 100,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= Self::spec_max_val(),
        ensures
            r == 0 <==> !Self::spec_exists_beautiful_d(a@),
            r != 0 <==> 1 <= r as int <= Self::spec_max_val() && Self::spec_beautiful(a@, r as int),
    {
        let n = a.len();
        let mut g_even = a[0];
        let mut i: usize = 2;
        while i < n {
            g_even = Self::gcd_two(g_even, a[i]);
            i = i + 2;
        }
        let mut g_odd = a[1];
        let mut i: usize = 3;
        while i < n {
            g_odd = Self::gcd_two(g_odd, a[i]);
            i = i + 2;
        }
        let mut ok_a = true;
        let mut j: usize = 1;
        while j < n {
            if a[j] % g_even == 0 {
                ok_a = false;
            }
            j = j + 2;
        }
        if ok_a {
            return g_even;
        }
        let mut ok_b = true;
        let mut j: usize = 0;
        while j < n {
            if a[j] % g_odd == 0 {
                ok_b = false;
            }
            j = j + 2;
        }
        if ok_b {
            return g_odd;
        }
        0
    }
}

}
