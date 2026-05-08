use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn count_people_helped(people: Vec<i64>, k: i64) -> usize {
        let mut gold: i64 = 0;
        let mut helped: usize = 0;
        let mut i: usize = 0;
        while i < people.len() {
            let ai = people[i];
            if ai >= k {
                gold = gold + ai;
            } else if ai == 0 && gold > 0 {
                gold = gold - 1;
                helped = helped + 1;
            }
            i = i + 1;
        }
        helped
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut case_id: usize = 0;
    while case_id < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let k: i64 = it.next().unwrap().parse().unwrap();
        let mut people: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            people.push(it.next().unwrap().parse().unwrap());
            i = i + 1;
        }
        let ans = Solution::count_people_helped(people, k);
        println!("{}", ans);
        case_id = case_id + 1;
    }
}
