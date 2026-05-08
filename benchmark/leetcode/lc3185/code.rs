impl Solution {
    pub fn count_complete_day_pairs(hours: Vec<i32>) -> i64 {
        let mut cnt: Vec<i64> = Vec::new();
        let mut c = 0usize;
        while c < 24 {
            cnt.push(0);
            c += 1;
        }
        let mut ans = 0i64;
        let mut i = 0usize;
        while i < hours.len() {
            let rem = (hours[i] % 24) as usize;
            let need = (24usize - rem) % 24usize;
            ans = ans.checked_add(cnt[need]).unwrap_or(ans);
            cnt[rem] = cnt[rem].checked_add(1).unwrap_or(cnt[rem]);
            i += 1;
        }
        ans
    }
}
