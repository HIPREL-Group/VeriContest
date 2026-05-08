struct Solution;
include!("code.rs");

fn check(nums: Vec<i32>, expected: i64) -> bool {
    let got = Solution::find_the_array_conc_val(nums.clone());
    if got != expected {
        println!("FAIL nums={:?} expected={} got={}", nums, expected, got);
        false
    } else {
        true
    }
}

fn main() {
    let mut passed = 0;
    let mut failed = 0;

    if check(vec![7, 52, 2, 4], 596) {
        passed += 1;
    } else {
        failed += 1;
    }

    if check(vec![5, 14, 13, 8, 12], 673) {
        passed += 1;
    } else {
        failed += 1;
    }

    println!("{} passed, {} failed", passed, failed);
    if failed > 0 {
        std::process::exit(1);
    }
}
