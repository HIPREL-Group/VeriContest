struct Solution;
include!("code.rs");

fn check(nums: Vec<i32>, expected: Vec<i32>) {
    let got = Solution::number_of_pairs(nums.clone());
    if got != expected {
        println!("FAIL nums={:?} expected={:?} got={:?}", nums, expected, got);
        std::process::exit(1);
    }
}

fn main() {
    check(vec![1, 3, 2, 1, 3, 2, 2], vec![3, 1]);
    check(vec![1, 1], vec![1, 0]);
    check(vec![0], vec![0, 1]);
    println!("3 passed, 0 failed");
}
