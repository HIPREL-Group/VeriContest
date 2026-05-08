struct Solution;
include!("code.rs");

fn check(num1: i32, num2: i32, expected: i32) -> bool {
    let got = Solution::sum(num1, num2);
    if got != expected {
        println!(
            "FAIL num1={} num2={} expected={} got={}",
            num1,
            num2,
            expected,
            got
        );
        false
    } else {
        true
    }
}

fn main() {
    let mut passed = 0;
    let mut failed = 0;

    if check(12, 5, 17) {
        passed += 1;
    } else {
        failed += 1;
    }

    if check(-10, 4, -6) {
        passed += 1;
    } else {
        failed += 1;
    }

    println!("{} passed, {} failed", passed, failed);
    if failed > 0 {
        std::process::exit(1);
    }
}
