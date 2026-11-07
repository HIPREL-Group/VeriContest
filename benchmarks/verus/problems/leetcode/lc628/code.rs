impl Solution {
    pub fn maximum_product(nums: Vec<i32>) -> i32
    {
        let n = nums.len();
        let mut top1: i32 = i32::MIN;
        let mut top2: i32 = i32::MIN;
        let mut top3: i32 = i32::MIN;
        let mut bot1: i32 = i32::MAX;
        let mut bot2: i32 = i32::MAX;

        let mut i = 0usize;
        while i < n
        {
            let v = nums[i];

            if v >= top1 {
                top3 = top2;
                top2 = top1;
                top1 = v;
            } else if v >= top2 {
                top3 = top2;
                top2 = v;
            } else if v >= top3 {
                top3 = v;
            }

            if v <= bot1 {
                bot2 = bot1;
                bot1 = v;
            } else if v <= bot2 {
                bot2 = v;
            }
            i += 1;
        }

        let p1 = top1 as i64 * top2 as i64 * top3 as i64;
        let p2 = bot1 as i64 * bot2 as i64 * top1 as i64;
        let best = if p1 >= p2 { p1 } else { p2 };

        best as i32
    }
}
