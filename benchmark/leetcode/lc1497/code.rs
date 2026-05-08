impl Solution {
    pub fn can_arrange(arr: Vec<i32>, k: i32) -> bool {
        let n = arr.len();
        let ku = k as usize;
        let mut count: Vec<i32> = Vec::new();
        let mut init = 0usize;
        while init < ku {
            count.push(0i32);
            init += 1;
        }
        let mut i = 0usize;
        while i < n {
            let elem = arr[i];
            let rem: i32;
            if elem >= 0 {
                rem = elem % k;
            } else {
                let neg_elem = -elem;
                let r = neg_elem % k;
                rem = if r == 0 { 0 } else { k - r };
            }
            let rem_u = rem as usize;
            count[rem_u] = count[rem_u] + 1;
            i += 1;
        }
        if count[0] % 2 != 0 {
            return false;
        }
        let mut j = 1usize;
        while j < ku {
            if count[j] != count[ku - j] {
                return false;
            }
            j += 1;
        }
        true
    }
}
