use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_has_common_divisor_ge_2(a: int, b: int) -> bool {
        exists|d: int|
            #![trigger a % d]
            2 <= d && a % d == 0 && b % d == 0
    }

    pub fn non_coprime_split(l: i32, r: i32) -> (res: Option<(i32, i32)>)
        requires
            l >= 1,
            l <= r,
            r <= 10_000_000,
            1 <= (l as int) <= (r as int) <= 10_000_000,
        ensures
            res != None::<(i32, i32)> ==> {
                let p = res->Some_0;
                &&& 1 <= (p.0 as int) <= 10_000_000
                &&& 1 <= (p.1 as int) <= 10_000_000
                &&& (l as int) <= (p.0 as int) + (p.1 as int) <= (r as int)
                &&& Self::spec_has_common_divisor_ge_2(p.0 as int, p.1 as int)
            },
            res == None::<(i32, i32)> <==> forall|a: int, b: int|
                (1 <= a && 1 <= b && (l as int) <= a + b <= (r as int))
                    ==> !Self::spec_has_common_divisor_ge_2(a, b),
    {
    }
}

}
