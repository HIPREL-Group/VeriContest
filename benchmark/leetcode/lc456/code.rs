impl Solution {
    pub fn find132pattern(nums: Vec<i32>) -> bool {
        if nums.len() < 3 {
            return false;
        }

        let mut min_left: Vec<i32> = Vec::new();
        min_left.push(nums[0]);
        
        let mut m: usize = 1;
        while m < nums.len() {
            let prev = min_left[m - 1];
            let curr = nums[m];
            if curr < prev {
                min_left.push(curr);
            } else {
                min_left.push(prev);
            }
            m += 1;
        }

        let mut stack: Vec<i32> = Vec::new();

        let mut j: usize = nums.len() - 1;

        while j > 0 {
            let current = nums[j];
            let l_min = min_left[j - 1];

            while stack.len() > 0 && *stack.last().unwrap() <= l_min {
                stack.pop();
            }

            if current > l_min {
                if stack.len() > 0 && *stack.last().unwrap() < current {
                    return true;
                }
                
                stack.push(current);
            }

            j -= 1;
        }
        
        false
    }
}
