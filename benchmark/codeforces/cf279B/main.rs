use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_books_read(books: Vec<i32>, t: i64) -> usize {
        let n = books.len();
        let mut left: usize = 0;
        let mut right: usize = 0;
        let mut sum: i64 = 0;
        let mut best: usize = 0;
        while right < n {
            sum = sum + books[right] as i64;
            right += 1;
            while sum > t && left < right {
                sum = sum - books[left] as i64;
                left += 1;
            }
            if right - left > best {
                best = right - left;
            }
        }
        best
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let nums: Vec<i64> = input
        .split_whitespace()
        .map(|s| s.parse::<i64>().expect("integer"))
        .collect();
    let n = nums[0] as usize;
    let t = nums[1];
    let mut books: Vec<i32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        books.push(nums[2 + i] as i32);
        i += 1;
    }
    let ans = Solution::max_books_read(books, t);
    println!("{}", ans);
}
