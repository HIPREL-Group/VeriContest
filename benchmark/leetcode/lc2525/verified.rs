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
        let l: i128 = length as i128;
        let w: i128 = width as i128;
        let h: i128 = height as i128;
        proof {
            assert(1 <= l <= 100000);
            assert(1 <= w <= 100000);
            assert(1 <= h <= 100000);
            assert(l * w <= 10000000000) by (nonlinear_arith)
                requires
                    1 <= l <= 100000,
                    1 <= w <= 100000,
            {
            }
        }
        let area: i128 = l * w;
        proof {
            assert(1 <= area <= 10000000000) by (nonlinear_arith)
                requires
                    area == l * w,
                    1 <= l <= 100000,
                    1 <= w <= 100000,
            {
            }
            assert(area * h <= 1000000000000000) by (nonlinear_arith)
                requires
                    1 <= area <= 10000000000,
                    1 <= h <= 100000,
            {
            }
        }
        let volume: i128 = area * h;
        let bulky: bool = length >= 10000 || width >= 10000 || height >= 10000 || volume >= 1_000_000_000;
        let heavy: bool = mass >= 100;
        if bulky && heavy {
            "Both".to_string()
        } else if bulky {
            "Bulky".to_string()
        } else if heavy {
            "Heavy".to_string()
        } else {
            "Neither".to_string()
        }
    }
}

}
