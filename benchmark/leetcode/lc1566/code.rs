impl Solution {
    pub fn contains_pattern(arr: Vec<i32>, m: i32, k: i32) -> bool {
        let n = arr.len();
        let mu = m as usize;
        let ku = k as usize;
        let mk = mu * ku;
        if mk > n {
            return false;
        }
        let target = (ku - 1) * mu;
        let mut consecutive: usize = 0;
        let mut pos: usize = mu;
        while pos < n {
            if arr[pos] == arr[pos - mu] {
                consecutive = consecutive + 1;
                if consecutive >= target {
                    return true;
                }
            } else {
                consecutive = 0;
            }
            pos = pos + 1;
        }
        false
    }
}
