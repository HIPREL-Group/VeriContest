impl Solution {
    pub fn max_lunch_joy(restaurants: Vec<(i64, i64)>, k: i64) -> i64 {
        let n = restaurants.len();
        let f0 = restaurants[0].0;
        let t0 = restaurants[0].1;
        let mut max_joy: i64 = if t0 <= k { f0 } else { f0 - t0 + k };
        let mut i: usize = 1;
        while i < n {
            let f = restaurants[i].0;
            let t = restaurants[i].1;
            let joy: i64 = if t <= k { f } else { f - t + k };
            if joy > max_joy {
                max_joy = joy;
            }
            i = i + 1;
        }
        max_joy
    }
}
