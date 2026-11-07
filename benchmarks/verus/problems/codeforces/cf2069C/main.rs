use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn count_beautiful_subsequences(a: Vec<i32>) -> u64 {
        let n = a.len();
        let mut result: u64 = 0;

        let mut i: usize = 0;
        while i < n {
            if a[i] == 3 && i >= 2 {
                let mut j: usize = 0;
                while j < i {
                    if a[j] == 1 {
                        let mut count_2s: u32 = 0;
                        let mut k: usize = j + 1;
                        while k < i {
                            if a[k] == 2 {
                                count_2s += 1;
                            }
                            k += 1;
                        }

                        let mut ways: u64 = 1;
                        let mut exp: u32 = 0;
                        while exp < count_2s {
                            ways = (ways * 2) % 998244353u64;
                            exp += 1;
                        }

                        let contrib = (((ways as u128) + 998244353u128 - 1)
                            % 998244353u128) as u64;
                        result = (result + contrib) % 998244353u64;
                    }
                    j += 1;
                }
            }
            i += 1;
        }

        result
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut tokens = input.split_whitespace();

    let t: usize = tokens.next().unwrap().parse().unwrap();
    for _ in 0..t {
        let n: usize = tokens.next().unwrap().parse().unwrap();
        let mut a = Vec::new();
        for _ in 0..n {
            let val: i32 = tokens.next().unwrap().parse().unwrap();
            a.push(val);
        }
        let result = Solution::count_beautiful_subsequences(a);
        println!("{}", result);
    }
}
