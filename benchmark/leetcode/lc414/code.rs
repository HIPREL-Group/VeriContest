impl Solution {
    pub fn third_max(nums: Vec<i32>) -> i32
    {
        let mut first: i32 = nums[0];
        let mut second: i32 = i32::MIN;
        let mut third: i32 = i32::MIN;
        let mut has_second = false;
        let mut has_third = false;
        
        let mut idx = 1;
        while idx < nums.len()
        {
            let num = nums[idx];
            let old_first = first;
            let old_second = second;
            let old_third = third;
            let old_has_second = has_second;
            let old_has_third = has_third;
            
            if num > first {
                third = second;
                has_third = has_second;
                second = first;
                has_second = true;
                first = num;
            } else if num < first && (!has_second || num > second) {
                third = second;
                has_third = has_second;
                second = num;
                has_second = true;
            } else if has_second && num < second && (!has_third || num > third) {
                third = num;
                has_third = true;
            } 
            
            idx += 1;
        }
        
        if has_third {
            third
        } else {
            first
        }
    }
}
