impl Solution {
    pub fn trap(height: Vec<i32>) -> i32 {
        let n = height.len();

        let mut left_max = Vec::with_capacity(n);
        left_max.push(height[0]);
        for i in 1..n
        {
            let prev = left_max[i - 1];
            let val = if height[i] > prev { height[i] } else { prev };
            left_max.push(val);
        }

        let mut right_max = Vec::with_capacity(n);
        for i in 0..n
        {
            right_max.push(height[i]);
        }
        for i in 1..n
        {
            let idx = n - 1 - i;
            if right_max[idx + 1] > right_max[idx] {
                right_max[idx] = right_max[idx + 1];
            }
        }

        let mut water: i32 = 0;
        for i in 0..n
        {
            let min_max = if left_max[i] < right_max[i] { left_max[i] } else { right_max[i] };
            water += min_max - height[i];
        }

        water
    }
}
