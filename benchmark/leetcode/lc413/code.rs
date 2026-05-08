fn number_of_arithmetic_slices(nums: Vec<i32>) -> i32 {
    let n = nums.len();
    if n < 3 {
        return 0;
    }
    let mut total = 0i32;
    let mut curr = 0i32;
    let mut i = 2;
    while i < n {
        if nums[i] - nums[i - 1] == nums[i - 1] - nums[i - 2] {
            curr = curr + 1;
            total = total + curr;
        } else {
            curr = 0;
        }
        i = i + 1;
    }
    total
}
