impl Solution {
    pub fn max_containers(n: i32, w: i32, max_weight: i32) -> i32 {
        let area = n * n;
        let by_weight = max_weight / w;
        if area <= by_weight {
            area
        } else {
            by_weight
        }
    }
}
