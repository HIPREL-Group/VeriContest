impl Solution {
    pub fn count_routes(locations: Vec<i32>, start: i32, finish: i32, fuel: i32) -> i32 {
        let n = locations.len();
        let fuel_cap: usize = (fuel as usize) + 1;
        let total_size: usize = n * fuel_cap;
        let modv: i64 = 1_000_000_007;
        let fi: usize = finish as usize;
        let mut dp: Vec<i64> = Vec::new();
        let mut idx: usize = 0;
        while idx < total_size {
            dp.push(0i64);
            idx = idx + 1;
        }
        let mut bf: usize = 0;
        while bf < fuel_cap {
            dp[fi * fuel_cap + bf] = 1i64;
            bf = bf + 1;
        }
        let mut f: usize = 1;
        while f < fuel_cap {
            let mut city: usize = 0;
            while city < n {
                let mut j: usize = 0;
                while j < n {
                    if j != city {
                        let cost_val: usize = if locations[city] >= locations[j] {
                            (locations[city] - locations[j]) as usize
                        } else {
                            (locations[j] - locations[city]) as usize
                        };
                        if f >= cost_val {
                            dp[city * fuel_cap + f] = (dp[city * fuel_cap + f] + dp[j * fuel_cap + (f - cost_val)]) % modv;
                        }
                    }
                    j = j + 1;
                }
                city = city + 1;
            }
            f = f + 1;
        }
        dp[start as usize * fuel_cap + fuel as usize] as i32
    }
}
