use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn bulky_spec(length: int, width: int, height: int) -> bool {
        length >= 10000 || width >= 10000 || height >= 10000 || length * width * height >= 1000000000
    }

    pub open spec fn heavy_spec(mass: int) -> bool {
        mass >= 100
    }

    pub open spec fn category_spec(length: int, width: int, height: int, mass: int) -> Seq<char> {
        if Self::bulky_spec(length, width, height) && Self::heavy_spec(mass) {
            "Both"@
        } else if Self::bulky_spec(length, width, height) {
            "Bulky"@
        } else if Self::heavy_spec(mass) {
            "Heavy"@
        } else {
            "Neither"@
        }
    }

    pub fn categorize_box(length: i32, width: i32, height: i32, mass: i32) -> (result: String)
        requires
            1 <= length <= 100000,
            1 <= width <= 100000,
            1 <= height <= 100000,
            1 <= mass <= 1000,
        ensures
            result@ == Self::category_spec(length as int, width as int, height as int, mass as int),
    {
    }
}

}
