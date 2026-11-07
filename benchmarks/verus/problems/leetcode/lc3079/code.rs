impl Solution {
    pub fn sum_of_encrypted_int(nums: Vec<i32>) -> i32 {
        let mut sum: i32 = 0;
        for i in 0..nums.len() {
            let n = nums[i];
            let enc: i32;
            if n < 10 {
                enc = n;
            } else if n < 100 {
                let d0 = n % 10;
                let d1 = n / 10;
                let m = if d0 >= d1 { d0 } else { d1 };
                enc = 11 * m;
            } else if n < 1000 {
                let d0 = n % 10;
                let d1 = (n / 10) % 10;
                let d2 = n / 100;
                let mut m = if d0 >= d1 { d0 } else { d1 };
                if d2 > m {
                    m = d2;
                }
                enc = 111 * m;
            } else {
                let d0 = n % 10;
                let d1 = (n / 10) % 10;
                let d2 = (n / 100) % 10;
                let d3 = n / 1000;
                let mut m = if d0 >= d1 { d0 } else { d1 };
                if d2 > m {
                    m = d2;
                }
                if d3 > m {
                    m = d3;
                }
                enc = 1111 * m;
            }
            sum = sum + enc;
        }
        sum
    }
}
