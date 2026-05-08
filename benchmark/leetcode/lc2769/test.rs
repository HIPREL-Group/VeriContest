struct Solution;
include!("code.rs");

fn main() {
    let mut passed = 0;
    let mut failed = 0;

    {
        let result = Solution::the_maximum_achievable_x(4, 1);
        if result == 6 {
            println!("Example 1: PASSED");
            passed += 1;
        } else {
            println!("Example 1: FAILED - expected 6, got {result}");
            failed += 1;
        }
    }

    {
        let result = Solution::the_maximum_achievable_x(3, 2);
        if result == 7 {
            println!("Example 2: PASSED");
            passed += 1;
        } else {
            println!("Example 2: FAILED - expected 7, got {result}");
            failed += 1;
        }
    }

    println!("\n{passed} passed, {failed} failed");
    if failed > 0 {
        std::process::exit(1);
    }
}
