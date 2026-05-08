fn longest_monotonic_subarray(nums: Vec<i32>) -> i32 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }
    let mut best = 1i32;
    let mut inc = 1i32;
    let mut dec = 1i32;
    let mut i = 1;
    while i < n {
        if nums[i] > nums[i - 1] {
            inc = inc + 1;
        } else {
            inc = 1;
        }
        if nums[i] < nums[i - 1] {
            dec = dec + 1;
        } else {
            dec = 1;
        }
        let cur = if inc > dec { inc } else { dec };
        if cur > best {
            best = cur;
        }
        i = i + 1;
    }
    best
}
