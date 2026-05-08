use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn gcd_spec(a: nat, b: nat) -> nat
        decreases b,
    {
        if b == 0 {
            a
        } else {
            Self::gcd_spec(b, (a % b) as nat)
        }
    }

    pub open spec fn solve_spec(a: Seq<i64>, b: Seq<i64>, i: int, cur_lcm: nat, cur_gcd: nat) -> nat
        decreases a.len() - i,
    {
        if i >= a.len() {
            1nat
        } else {
            let g = Self::gcd_spec(cur_lcm, b[i] as nat);
            if g > 0 {
                let q = cur_lcm / g;
                if q <= 18_446_744_073_709_551_615nat / (b[i] as nat) {
                    let next_lcm = q * b[i] as nat;
                    let next_gcd = Self::gcd_spec(cur_gcd, (a[i] as int * b[i] as int) as nat);
                    
                    if next_lcm > 0 && next_gcd % next_lcm == 0 {
                        Self::solve_spec(a, b, i + 1, next_lcm, next_gcd)
                    } else {
                        1nat + Self::solve_spec(a, b, i + 1, b[i] as nat, (a[i] as int * b[i] as int) as nat)
                    }
                } else {
                    1nat + Self::solve_spec(a, b, i + 1, b[i] as nat, (a[i] as int * b[i] as int) as nat)
                }
            } else {
                1nat + Self::solve_spec(a, b, i + 1, b[i] as nat, (a[i] as int * b[i] as int) as nat)
            }
        }
    }

    pub open spec fn solve(a: Seq<i64>, b: Seq<i64>) -> nat {
        if a.len() == 0 {
            0
        } else {
            Self::solve_spec(a, b, 1, b[0] as nat, (a[0] as int * b[0] as int) as nat)
        }
    }

    pub fn gcd(a: u64, b: u64) -> (res: u64)
        requires
            a >= 0, b >= 0,
        ensures
            res as nat == Self::gcd_spec(a as nat, b as nat),
    {
        let mut x = a;
        let mut y = b;
        while y != 0
            invariant
                Self::gcd_spec(x as nat, y as nat) == Self::gcd_spec(a as nat, b as nat),
            decreases y,
        {
            let t = y;
            y = x % y;
            x = t;
        }
        x
    }

    pub fn min_tags(a: Vec<i64>, b: Vec<i64>) -> (result: u64)
        requires
            a.len() == b.len(),
            1 <= a.len() <= 200_000,
            forall |i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
            forall |i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= 10_000,
        ensures
            result as nat == Self::solve(a@, b@),
    {
        let n = a.len();
        if n == 0 {
            return 0;
        }

        proof {
            assert((a[0] as u64) * (b[0] as u64) <= 10_000_000_000_000u64) by (nonlinear_arith)
                requires 0 <= a[0 as int] as u64, a[0 as int] as u64 <= 1_000_000_000, 
                         0 <= b[0 as int] as u64, b[0 as int] as u64 <= 10_000;
        }

        let mut closed: u64 = 0;
        let mut cur_lcm: u64 = b[0] as u64;
        let mut cur_gcd: u64 = (a[0] as u64) * (b[0] as u64);
        let mut i: usize = 1;

        while i < n
            invariant
                n == a.len(),
                n == b.len(),
                1 <= n <= 200_000,
                1 <= i <= n,
                closed <= i as u64,
                forall |k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 1_000_000_000,
                forall |k: int| 0 <= k < b.len() ==> 1 <= #[trigger] b[k] <= 10_000,
                closed as nat + Self::solve_spec(a@, b@, i as int, cur_lcm as nat, cur_gcd as nat) 
                    == Self::solve(a@, b@),
            decreases n - i,
        {
            let aval = a[i] as u64;
            let bval = b[i] as u64;

            proof {
                assert(aval <= 1_000_000_000);
                assert(bval <= 10_000);
            }

            let g = Self::gcd(cur_lcm, bval);
            if g > 0 {
                let q = cur_lcm / g;
                if q <= 18_446_744_073_709_551_615u64 / bval {
                    proof {
                        assert(q * bval <= 18_446_744_073_709_551_615u64) by (nonlinear_arith)
                            requires q <= 18_446_744_073_709_551_615u64 / bval, bval > 0;
                        assert(aval * bval <= 10_000_000_000_000u64) by (nonlinear_arith)
                            requires aval <= 1_000_000_000, bval <= 10_000;
                    }
                    let next_lcm = q * bval;
                    let next_gcd = Self::gcd(cur_gcd, aval * bval);

                    if next_lcm > 0 && next_gcd % next_lcm == 0 {
                        cur_lcm = next_lcm;
                        cur_gcd = next_gcd;
                    } else {
                        closed = closed + 1;
                        cur_lcm = bval;
                        cur_gcd = aval * bval;
                    }
                } else {
                    proof {
                        assert(aval * bval <= 10_000_000_000_000u64) by (nonlinear_arith)
                            requires aval <= 1_000_000_000, bval <= 10_000;
                    }
                    closed = closed + 1;
                    cur_lcm = bval;
                    cur_gcd = aval * bval;
                }
            } else {
                proof {
                    assert(aval * bval <= 10_000_000_000_000u64) by (nonlinear_arith)
                        requires aval <= 1_000_000_000, bval <= 10_000;
                }
                closed = closed + 1;
                cur_lcm = bval;
                cur_gcd = aval * bval;
            }
            i = i + 1;
        }
        closed + 1
    }
}

}
