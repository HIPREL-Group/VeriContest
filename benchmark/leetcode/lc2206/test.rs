struct Solution;
include!("code.rs");

fn check(nums: Vec<i32>, expected: bool) {
    let got = Solution::divide_array(nums.clone());
    if got != expected {
        println!("FAIL nums={:?} expected={} got={}", nums, expected, got);
        std::process::exit(1);
    }
}

fn main() {
    check(vec![3, 2, 3, 2, 2, 2], true);
    check(vec![1, 2, 3, 4], false);
    println!("2 passed, 0 failed");
}
