impl Solution {
    pub fn max_length(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut ans: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            let mut sum2: i32 = 0;
            let mut min2: i32 = 4;
            let mut max2: i32 = 0;
            let mut sum3: i32 = 0;
            let mut min3: i32 = 3;
            let mut max3: i32 = 0;
            let mut sum5: i32 = 0;
            let mut min5: i32 = 2;
            let mut max5: i32 = 0;
            let mut sum7: i32 = 0;
            let mut min7: i32 = 2;
            let mut max7: i32 = 0;
            let mut best_i: i32 = 0;
            let mut j: usize = i;
            while j < n {
                let x = nums[j];
                let e2: i32 =
                    if x == 8 { 3 } else if x == 4 { 2 } else if x == 2 || x == 6 || x == 10 { 1 } else { 0 };
                let e3: i32 = if x == 9 { 2 } else if x == 3 || x == 6 { 1 } else { 0 };
                let e5: i32 = if x == 5 || x == 10 { 1 } else { 0 };
                let e7: i32 = if x == 7 { 1 } else { 0 };

                sum2 = sum2 + e2;
                if e2 < min2 {
                    min2 = e2;
                }
                if e2 > max2 {
                    max2 = e2;
                }

                sum3 = sum3 + e3;
                if e3 < min3 {
                    min3 = e3;
                }
                if e3 > max3 {
                    max3 = e3;
                }

                sum5 = sum5 + e5;
                if e5 < min5 {
                    min5 = e5;
                }
                if e5 > max5 {
                    max5 = e5;
                }

                sum7 = sum7 + e7;
                if e7 < min7 {
                    min7 = e7;
                }
                if e7 > max7 {
                    max7 = e7;
                }

                let cand: i32 =
                    if sum2 == (min2 + max2) && sum3 == (min3 + max3) && sum5 == (min5 + max5) && sum7 == (min7 + max7) {
                        (j - i + 1) as i32
                    } else {
                        0
                    };
                if cand > best_i {
                    best_i = cand;
                }

                j = j + 1;
            }
            if best_i > ans {
                ans = best_i;
            }
            i = i + 1;
        }
        ans
    }
}
