struct Solution;
include!("code.rs");

fn check(n: i32, expected: i32) -> bool {
    let got = Solution::number_of_cuts(n);
    if got != expected {
        println!("FAIL n={} expected={} got={}", n, expected, got);
        false
    } else {
        true
    }
}

fn main() {
    let mut passed = 0;
    let mut failed = 0;

    if check(4, 2) {
        passed += 1;
    } else {
        failed += 1;
    }

    if check(3, 3) {
        passed += 1;
    } else {
        failed += 1;
    }

    println!("{} passed, {} failed", passed, failed);
    if failed > 0 {
        std::process::exit(1);
    }
}
