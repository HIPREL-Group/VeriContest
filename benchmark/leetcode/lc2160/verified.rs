use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn digit0(num: int) -> int {
    num / 1000
}

pub open spec fn digit1(num: int) -> int {
    (num / 100) % 10
}

pub open spec fn digit2(num: int) -> int {
    (num / 10) % 10
}

pub open spec fn digit3(num: int) -> int {
    num % 10
}

pub open spec fn sorted_d1(num: int) -> int {
    let a = digit0(num);
    let b = digit1(num);
    let c = digit2(num);
    let d = digit3(num);
    let ab_lo = if a < b { a } else { b };
    let cd_lo = if c < d { c } else { d };
    if ab_lo < cd_lo { ab_lo } else { cd_lo }
}

pub open spec fn sorted_d4(num: int) -> int {
    let a = digit0(num);
    let b = digit1(num);
    let c = digit2(num);
    let d = digit3(num);
    let ab_hi = if a < b { b } else { a };
    let cd_hi = if c < d { d } else { c };
    if ab_hi < cd_hi { cd_hi } else { ab_hi }
}

pub open spec fn sorted_d2(num: int) -> int {
    let a = digit0(num);
    let b = digit1(num);
    let c = digit2(num);
    let d = digit3(num);
    let ab_lo = if a < b { a } else { b };
    let ab_hi = if a < b { b } else { a };
    let cd_lo = if c < d { c } else { d };
    let cd_hi = if c < d { d } else { c };
    let m1 = if ab_lo < cd_lo { cd_lo } else { ab_lo };
    let m2 = if ab_hi < cd_hi { ab_hi } else { cd_hi };
    if m1 < m2 { m1 } else { m2 }
}

pub open spec fn sorted_d3(num: int) -> int {
    let a = digit0(num);
    let b = digit1(num);
    let c = digit2(num);
    let d = digit3(num);
    let ab_lo = if a < b { a } else { b };
    let ab_hi = if a < b { b } else { a };
    let cd_lo = if c < d { c } else { d };
    let cd_hi = if c < d { d } else { c };
    let m1 = if ab_lo < cd_lo { cd_lo } else { ab_lo };
    let m2 = if ab_hi < cd_hi { ab_hi } else { cd_hi };
    if m1 < m2 { m2 } else { m1 }
}

impl Solution {
    pub fn minimum_sum(num: i32) -> (result: i32)
        requires
            1000 <= num <= 9999,
        ensures
            result as int == (sorted_d1(num as int) + sorted_d2(num as int)) * 10
                + sorted_d3(num as int) + sorted_d4(num as int),
    {
        let a = num / 1000;
        let b = (num / 100) % 10;
        let c = (num / 10) % 10;
        let d = num % 10;

        let ab_lo = if a < b { a } else { b };
        let ab_hi = if a < b { b } else { a };
        let cd_lo = if c < d { c } else { d };
        let cd_hi = if c < d { d } else { c };

        let d1 = if ab_lo < cd_lo { ab_lo } else { cd_lo };
        let d4 = if ab_hi < cd_hi { cd_hi } else { ab_hi };
        let m1 = if ab_lo < cd_lo { cd_lo } else { ab_lo };
        let m2 = if ab_hi < cd_hi { ab_hi } else { cd_hi };
        let d2 = if m1 < m2 { m1 } else { m2 };
        let d3 = if m1 < m2 { m2 } else { m1 };

        proof {
            assert(digit0(num as int) == a as int);
            assert(digit1(num as int) == b as int);
            assert(digit2(num as int) == c as int);
            assert(digit3(num as int) == d as int);

            assert(sorted_d1(num as int) == d1 as int);
            assert(sorted_d2(num as int) == d2 as int);
            assert(sorted_d3(num as int) == d3 as int);
            assert(sorted_d4(num as int) == d4 as int);
        }

        (d1 + d2) * 10 + d3 + d4
    }
}

}
