impl Solution {
    pub fn sum_four_divisors(nums: Vec<i32>) -> i32 {
        let mut total: i32 = 0;
        let n = nums.len();
        let mut i: usize = 0;
        while i < n {
            let num = nums[i];
            let mut d: i32 = 1;
            let mut count: i32 = 0;
            let mut sum: i32 = 0;
            while d * d <= num && count <= 4 {
                if num % d == 0 {
                    count = count + 1;
                    sum = sum + d;
                    let other: i32 = num / d;
                    if other != d {
                        count = count + 1;
                        sum = sum + other;
                    }
                }
                d = d + 1;
            }
            if count == 4 {
                total = total + sum;
            }
            i = i + 1;
        }
        total
    }
}
