impl Solution {
    pub fn number_of_points(nums: Vec<Vec<i32>>) -> i32 {
        let mut covered = vec![false; 101];
        let mut i: usize = 0;
        while i < nums.len() {
            if nums[i].len() >= 2 {
                let a = nums[i][0];
                let b = nums[i][1];
                let mut l = if a <= b { a } else { b };
                let mut r = if a <= b { b } else { a };
                if l < 1 { l = 1; }
                if r > 100 { r = 100; }
                if l <= r {
                    let mut x: i32 = l;
                    while x <= r {
                        covered[x as usize] = true;
                        x = x + 1;
                    }
                }
            }
            i = i + 1;
        }

        let mut ans: i32 = 0;
        i = 1;
        while i <= 100 {
            if covered[i] {
                ans = ans + 1;
            }
            i = i + 1;
        }
        ans
    }
}
