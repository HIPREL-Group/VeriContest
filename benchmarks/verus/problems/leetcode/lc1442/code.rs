impl Solution {
    pub fn count_triplets(arr: Vec<i32>) -> i32 {
        let n = arr.len();
        let mut prefix: Vec<i32> = Vec::new();
        prefix.push(0);
        let mut i: usize = 0;
        while i < n {
            let prev = prefix[i];
            prefix.push(prev ^ arr[i]);
            i = i + 1;
        }
        let mut keys: Vec<i32> = Vec::new();
        let mut cnts: Vec<i32> = Vec::new();
        let mut sums: Vec<i32> = Vec::new();
        let mut count: i32 = 0;
        let mut m: usize = 0;
        while m <= n {
            let pv = prefix[m];
            let mut found: bool = false;
            let mut idx: usize = 0;
            let keys_len = keys.len();
            while idx < keys_len {
                if keys[idx] == pv {
                    found = true;
                    if m > 0 {
                        count = count + cnts[idx] * ((m as i32) - 1) - sums[idx];
                    }
                    cnts[idx] = cnts[idx] + 1;
                    sums[idx] = sums[idx] + m as i32;
                    idx = keys_len;
                } else {
                    idx = idx + 1;
                }
            }
            if !found {
                keys.push(pv);
                cnts.push(1);
                sums.push(m as i32);
            }
            m = m + 1;
        }
        count
    }
}
