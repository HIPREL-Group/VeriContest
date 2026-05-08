impl Solution {
    pub fn maximum_even_sum(a: i128, b: i128) -> i128 {
        let mut k: i128 = 1;
        let mut found: bool = false;
        let mut best: i128 = -1;
        while k <= b {
            let cur_k = k;
            let mut cur_valid = false;
            let mut cur_even = false;
            let mut cur_sum: i128 = 0;
            if b % cur_k == 0 {
                cur_valid = true;
                let prod = a * cur_k;
                cur_sum = prod + b / cur_k;
                cur_even = cur_sum % 2 == 0;

                if cur_even {
                    if !found || cur_sum > best {
                        best = cur_sum;
                        found = true;
                    }
                }
            }
            k = k + 1;
        }
        if found {
            best
        } else {
            -1
        }
    }
}