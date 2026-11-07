impl Solution {
    pub fn can_three_parts_equal_sum(arr: Vec<i32>) -> bool {
        let n = arr.len();
        let mut total: i128 = 0;
        let mut i: usize = 0;
        while i < n {
            total = total + arr[i] as i128;
            i += 1;
        }

        let target = total / 3;
        if target * 3 != total {
            return false;
        }

        let mut prefix: i128 = 0;
        i = 0;
        while i < n - 2 {
            let next_prefix = prefix + arr[i] as i128;
            prefix = next_prefix;
            if prefix == target {
                let first_end = i + 1;
                i += 1;
                while i < n - 1 {
                    let next_prefix = prefix + arr[i] as i128;
                    prefix = next_prefix;
                    if prefix == 2 * target {
                        return true;
                    }
                    i += 1;
                }
                return false;
            }
            i += 1;
        }

        false
    }
}
