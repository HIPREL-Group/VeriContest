use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn find_covering_segment(left: Vec<i32>, right: Vec<i32>) -> i32 {
        let mut candidate = 0usize;
        let mut i = 1usize;
        while i < left.len() {
            if left[i] < left[candidate] || (left[i] == left[candidate] && right[candidate] < right[i]) {
                candidate = i;
            }
            i += 1;
        }

        let mut j = 0usize;
        while j < left.len() {
            if left[candidate] > left[j] || right[j] > right[candidate] {
                return 0;
            }
            j += 1;
        }

        candidate as i32 + 1
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();
    let n = it.next().expect("n").parse::<usize>().expect("usize");
    let mut left = Vec::with_capacity(n);
    let mut right = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        left.push(it.next().expect("left").parse::<i32>().expect("i32"));
        right.push(it.next().expect("right").parse::<i32>().expect("i32"));
        i += 1;
    }
    let ans = Solution::find_covering_segment(left, right);
    if ans == 0 {
        println!("-1");
    } else {
        println!("{}", ans);
    }
}
