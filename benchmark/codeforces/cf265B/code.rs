impl Solution {
    pub fn min_time(heights: Vec<i32>) -> i64 {
        let n = heights.len();
        let mut time = 0i64;
        let mut current_height = 0i32;
        let mut i: usize = 0;
        while i < n {
            let target_height = heights[i];
            let climb: i64 = if target_height > current_height {
                (target_height - current_height) as i64
            } else {
                (current_height - target_height) as i64
            };
            time = time + climb;
            current_height = target_height;
            time = time + 1;
            if i < n - 1 {
                let next_tree_height = heights[i + 1];
                let max_jump_height = next_tree_height + 1;
                if current_height > max_jump_height {
                    let climb_down = (current_height - max_jump_height) as i64;
                    time = time + climb_down;
                    current_height = max_jump_height;
                }
                time = time + 1;
            }
            i = i + 1;
        }
        time
    }
}
