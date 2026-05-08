impl Solution {
    pub fn minimum_sum(num: i32) -> i32 {
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

        (d1 + d2) * 10 + d3 + d4
    }
}
