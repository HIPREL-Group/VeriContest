use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn remove_smallest_possible(a: Vec<i32>) -> bool {
        let n = a.len();
        if n == 1 {
            return true;
        }
        let mut arr = Vec::new();
        let mut i = 0usize;
        while i < n {
            arr.push(a[i]);
            i += 1;
        }
        i = 0usize;
        while i < n {
            let mut min_idx = i;
            let mut j = i + 1;
            while j < n {
                if arr[j] < arr[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }
            if i != min_idx {
                let tmp = arr[i];
                arr[i] = arr[min_idx];
                arr[min_idx] = tmp;
            }
            i += 1;
        }
        let mut k = 0usize;
        while k + 1 < n {
            if (arr[k + 1] as i64) > (arr[k] as i64) + 1 {
                return false;
            }
            k += 1;
        }
        true
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let v: i32 = it.next().unwrap().parse().unwrap();
            a.push(v);
            i = i + 1;
        }
        let ok = Solution::remove_smallest_possible(a);
        if ok {
            println!("YES");
        } else {
            println!("NO");
        }
        k = k + 1;
    }
}
