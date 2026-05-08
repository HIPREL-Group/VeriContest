impl Solution {
    pub fn max_decorated_tables(r: i64, g: i64, b: i64) -> i64 {
        let sum = r + g + b;
        let rg_max = if r >= g { r } else { g };
        let largest = if rg_max >= b { rg_max } else { b };
        let limit_by_total = sum / 3;
        let limit_by_dominant = sum - largest;
        if limit_by_total <= limit_by_dominant {
            limit_by_total
        } else {
            limit_by_dominant
        }
    }
}
