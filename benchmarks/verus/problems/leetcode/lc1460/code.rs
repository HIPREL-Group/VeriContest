impl Solution {
    pub fn can_be_equal(target: Vec<i32>, arr: Vec<i32>) -> bool {
        let n = target.len();
        let mut counts: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < 1001 {
            counts.push(0i32);
            k = k + 1;
        }
        let mut i: usize = 0;
        while i < n {
            let tv = target[i];
            let av = arr[i];
            counts[tv as usize] = counts[tv as usize] + 1;
            counts[av as usize] = counts[av as usize] - 1;
            i = i + 1;
        }
        let mut k2: usize = 0;
        while k2 < 1001 {
            if counts[k2] != 0 {
                return false;
            }
            k2 = k2 + 1;
        }
        true
    }
}
