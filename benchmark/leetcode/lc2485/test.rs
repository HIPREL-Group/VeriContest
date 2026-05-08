struct Solution;
include!("code.rs");

fn check(n: i32, expected: i32) {
    let got = Solution::pivot_integer(n);
    if got != expected {
        println!("FAIL n={} expected={} got={}", n, expected, got);
        std::process::exit(1);
    }
}

fn main() {
    check(8, 6);
    check(1, 1);
    check(4, -1);
    println!("3 passed, 0 failed");
}
