use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn is_spruce(n: usize, p: Vec<usize>) -> bool {
        let mut is_p = Vec::new();
        let mut i = 0;
        while i < n {
            is_p.push(false);
            i += 1;
        }

        i = 0;
        while i < p.len() {
            let parent = p[i];
            is_p[parent] = true;
            i += 1;
        }

        let mut leaf_children_count = Vec::new();
        let mut j = 0;
        while j < n {
            leaf_children_count.push(0);
            j += 1;
        }

        j = 0;
        while j < p.len() {
            let is_leaf_node = !is_p[j + 1];
            if is_leaf_node {
                let parent = p[j];
                let cnt = leaf_children_count[parent];
                leaf_children_count[parent] = cnt + 1;
            }
            j += 1;
        }

        let mut k = 0;
        let mut ans = true;
        while k < n {
            if is_p[k] && leaf_children_count[k] < 3 {
                ans = false;
            }
            k += 1;
        }

        ans
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(line1)) = lines.next() {
        if let Ok(n) = line1.trim().parse::<usize>() {
            let mut p = Vec::new();
            for _ in 0..(n - 1) {
                if let Some(Ok(line)) = lines.next() {
                    if let Ok(pi) = line.trim().parse::<usize>() {
                        p.push(pi - 1);
                    }
                }
            }
            let result = Solution::is_spruce(n, p);
            if result {
                println!("Yes");
            } else {
                println!("No");
            }
        }
    }
}
