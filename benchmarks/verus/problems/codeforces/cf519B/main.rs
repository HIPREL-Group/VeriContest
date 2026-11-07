use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn find_compilation_errors(first: Vec<i64>, second: Vec<i64>, third: Vec<i64>) -> (i64, i64) {
        let mut sum_first: i64 = 0;
        let mut i: usize = 0;
        while i < first.len() {
            sum_first = sum_first + first[i];
            i = i + 1;
        }

        let mut sum_second: i64 = 0;
        let mut j: usize = 0;
        while j < second.len() {
            sum_second = sum_second + second[j];
            j = j + 1;
        }

        let mut sum_third: i64 = 0;
        let mut k: usize = 0;
        while k < third.len() {
            sum_third = sum_third + third[k];
            k = k + 1;
        }

        let deleted_first = sum_first - sum_second;
        let deleted_second = sum_second - sum_third;
        (deleted_first, deleted_second)
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let n: usize = it.next().unwrap().parse().unwrap();
    let mut first: Vec<i64> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        first.push(it.next().unwrap().parse().unwrap());
        i += 1;
    }

    let mut second: Vec<i64> = Vec::with_capacity(n - 1);
    let mut j: usize = 0;
    while j + 1 < n {
        second.push(it.next().unwrap().parse().unwrap());
        j += 1;
    }

    let mut third: Vec<i64> = Vec::with_capacity(n - 2);
    let mut k: usize = 0;
    while k + 2 < n {
        third.push(it.next().unwrap().parse().unwrap());
        k += 1;
    }

    let answer = Solution::find_compilation_errors(first, second, third);
    println!("{}", answer.0);
    println!("{}", answer.1);
}
