use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn build_number(s: int, d: int) -> int
    decreases d,
{
    if s <= 0 || d <= 0 {
        0int
    } else if d <= s {
        build_number(s - d, d - 1) * 10 + d
    } else {
        build_number(s, d - 1)
    }
}

proof fn lemma_build_nonneg(s: int, d: int)
    requires 0 <= s, 0 <= d,
    ensures build_number(s, d) >= 0,
    decreases d,
{
    if s <= 0 || d <= 0 {
    } else if d <= s {
        lemma_build_nonneg(s - d, d - 1);
    } else {
        lemma_build_nonneg(s, d - 1);
    }
}

spec fn pow10(d: int) -> int
    decreases if d >= 0 { d } else { 0 },
{
    if d <= 0 { 1int } else { pow10(d - 1) * 10 }
}

proof fn lemma_pow10_pos(d: int)
    requires 0 <= d,
    ensures pow10(d) >= 1,
    decreases d,
{
    if d == 0 {
    } else {
        lemma_pow10_pos(d - 1);
    }
}

proof fn lemma_build_upper(s: int, d: int)
    requires 0 <= s, 0 <= d <= 9,
    ensures
        build_number(s, d) >= 0,
        build_number(s, d) < pow10(d),
    decreases d,
{
    if s <= 0 || d <= 0 {
        lemma_pow10_pos(d);
    } else if d <= s {
        lemma_build_upper(s - d, d - 1);
        lemma_pow10_pos(d - 1);
        assert(pow10(d) == pow10(d - 1) * 10);  
        assert((pow10(d - 1) - 1) * 10 + d < pow10(d)) by (nonlinear_arith)
            requires
                d >= 1,
                d <= 9,
                pow10(d) == pow10(d - 1) * 10,
                pow10(d - 1) >= 1;
    } else {
        lemma_build_upper(s, d - 1);
        lemma_pow10_pos(d - 1);
        assert(pow10(d) == pow10(d - 1) * 10);
    }
}

proof fn lemma_pow10_d_eq(d: int)
    requires d == 9,
    ensures pow10(d) == 1000000000int,
{
    reveal_with_fuel(pow10, 11);
}

proof fn lemma_build_upper_9(s: int)
    requires 0 <= s,
    ensures
        build_number(s, 9) >= 0,
        build_number(s, 9) < 1000000000int,
{
    lemma_build_upper(s, 9);
    lemma_pow10_d_eq(9);
}

impl Solution {
    pub fn min_varied(s: u32) -> (result: u32)
        requires
            1 <= s <= 45,
        ensures
            result as int == build_number(s as int, 9),
    {
        let mut num: u64 = 0;
        let mut mul: u64 = 1;
        let mut rem: u32 = s;
        let mut d: u32 = 9;
        proof {
            lemma_build_upper_9(s as int);
            lemma_build_upper(s as int, 9);
            
            lemma_pow10_d_eq(9);
        }
        while d >= 1
            invariant
                d <= 9,
                rem <= s,
                rem <= 45,
                s <= 45,
                1 <= s,
                mul >= 1,
                mul <= 1000000000u64,
                num <= 999999999u64,
                build_number(s as int, 9) == num as int + build_number(rem as int, d as int) * (mul as int),
                build_number(s as int, 9) >= 0,
                build_number(s as int, 9) < 1000000000int,
                build_number(rem as int, d as int) >= 0,
                build_number(rem as int, d as int) < pow10(d as int),
                pow10(d as int) * (mul as int) <= 1000000000int,
            decreases d,
        {
            let old_d = d;
            let old_mul = mul;
            proof {
                lemma_pow10_pos(d as int);
                lemma_pow10_pos((d - 1) as int);
            }
            if d <= rem {
                proof {
                    assert(build_number(rem as int, d as int)
                        == build_number(rem as int - d as int, d as int - 1) * 10 + d as int);
                    lemma_build_upper(rem as int - d as int, d as int - 1);
                    assert(num as int + d as int * mul as int + build_number(rem as int - d as int, d as int - 1) * (mul as int * 10)
                        == num as int + (d as int + build_number(rem as int - d as int, d as int - 1) * 10) * mul as int) by (nonlinear_arith);
                    
                    assert(pow10(d as int) == pow10((d - 1) as int) * 10);
                    
                    assert(pow10((d - 1) as int) * (mul as int * 10) == pow10(d as int) * (mul as int)) by (nonlinear_arith)
                        requires pow10(d as int) == pow10((d - 1) as int) * 10;
                }
                proof {
                    
                    
                    
                    
                    lemma_pow10_pos((old_d - 1) as int);
                    assert(pow10((old_d - 1) as int) * ((old_mul as int) * 10) == pow10(old_d as int) * (old_mul as int)) by (nonlinear_arith)
                        requires pow10(old_d as int) == pow10((old_d - 1) as int) * 10;
                    assert(pow10((old_d - 1) as int) * ((old_mul as int) * 10) <= 1000000000int);
                    assert((old_mul as int) * 10 <= 1000000000int) by (nonlinear_arith)
                        requires
                            pow10((old_d - 1) as int) >= 1,
                            pow10((old_d - 1) as int) * ((old_mul as int) * 10) <= 1000000000int,
                            old_mul as int >= 0;
                }
                let new_num: u64 = num + (d as u64) * mul;
                let new_mul: u64 = mul * 10;
                let new_rem: u32 = rem - d;
                num = new_num;
                mul = new_mul;
                rem = new_rem;
                proof {
                    
                    
                    assert(pow10((old_d - 1) as int) * (old_mul as int * 10) == pow10(old_d as int) * (old_mul as int));
                }
            } else {
                proof {
                    assert(build_number(rem as int, d as int) == build_number(rem as int, d as int - 1));
                    lemma_build_upper(rem as int, (d - 1) as int);
                    assert(pow10(d as int) == pow10((d - 1) as int) * 10);
                    lemma_pow10_pos((d - 1) as int);
                    
                    
                    assert(pow10(d as int) * (mul as int) == 10 * (pow10((d - 1) as int) * (mul as int))) by (nonlinear_arith)
                        requires pow10(d as int) == pow10((d - 1) as int) * 10;
                }
            }
            d = d - 1;
        }
        proof {
            
            assert(d == 0);
            assert(build_number(rem as int, 0) == 0);
            assert(build_number(s as int, 9) == num as int);
        }
        num as u32
    }
}

}
