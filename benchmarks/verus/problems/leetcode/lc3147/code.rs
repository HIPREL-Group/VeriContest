impl Solution {
    pub fn maximum_energy(energy: Vec<i32>, k: i32) -> i32 {
        let n = energy.len();
        let ku = k as usize;
        let mut arr = energy.clone();

        let mut idx = n;
        while idx > 0 {
            idx -= 1;
            if idx + ku < n {
                let sum = arr[idx] as i64 + arr[idx + ku] as i64;
                let v = if sum < i32::MIN as i64 || sum > i32::MAX as i64 {
                    0
                } else {
                    sum as i32
                };
                arr[idx] = v;
            }
        }

        let mut ans = arr[0];
        let mut j = 1usize;
        while j < n {
            if arr[j] > ans {
                ans = arr[j];
            }
            j += 1;
        }
        ans
    }
}
