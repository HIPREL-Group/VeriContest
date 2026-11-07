impl Solution {
    pub fn number_of_alternating_groups(colors: Vec<i32>, k: i32) -> i32 {
        let n = colors.len();
        let ku = k as usize;
        let mut ans = 0i32;
        let mut cnt = 1usize;
        let mut i = 1usize;
        while i < n + ku - 1 {
            let cur = i % n;
            let prev = (i - 1) % n;
            if colors[cur] != colors[prev] {
                cnt = if cnt < ku { cnt + 1 } else { ku };
            } else {
                cnt = 1;
            }
            if cnt >= ku {
                ans = ans.checked_add(1).unwrap_or(ans);
            }
            i += 1;
        }
        ans
    }
}
