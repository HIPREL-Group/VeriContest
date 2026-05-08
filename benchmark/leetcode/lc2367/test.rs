struct Solution;
include!("code.rs");

fn check(nums: Vec<i32>, diff: i32, expected: i32) {
    let got = Solution::arithmetic_triplets(nums.clone(), diff);
    if got != expected {
        println!("FAIL nums={:?} diff={} expected={} got={}", nums, diff, expected, got);
        std::process::exit(1);
    }
}

fn main() {
    check(vec![0, 1, 4, 6, 7, 10], 3, 2);
    check(vec![4, 5, 6, 7, 8, 9], 2, 2);
    println!("2 passed, 0 failed");
}
