struct Solution;
include!("code.rs");

fn check(num: i32, expected: i32) {
    let got = Solution::split_num(num);
    if got != expected {
        println!("FAIL num={} expected={} got={}", num, expected, got);
        std::process::exit(1);
    }
}

fn main() {
    check(4325, 59);
    check(687, 75);
    println!("2 passed, 0 failed");
}
