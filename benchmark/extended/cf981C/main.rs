use std::io::{self, BufRead};

pub struct Solution;

impl Solution {
    pub fn useful_decomposition(n: usize, u_edges: Vec<usize>, v_edges: Vec<usize>) -> (bool, usize, Vec<usize>) {
        let mut degrees: Vec<i32> = Vec::new();
        let mut i = 0;
        while i <= n {
            degrees.push(0);
            i += 1;
        }

        i = 0;
        while i < n - 1 {
            let u = u_edges[i];
            let v = v_edges[i];
            
            degrees[u] = degrees[u] + 1;
            degrees[v] = degrees[v] + 1;
            
            i += 1;
        }

        let mut high_count = 0;
        let mut center = 1;
        i = 1;
        while i <= n {
            if degrees[i] >= 3 {
                high_count += 1;
                center = i;
            }
            i += 1;
        }

        if high_count > 1 {
            (false, 0, Vec::new())
        } else {
            let mut leaves: Vec<usize> = Vec::new();
            i = 1;
            while i <= n {
                if degrees[i] == 1 && i != center {
                    leaves.push(i);
                }
                i += 1;
            }
            (true, center, leaves)
        }
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(line1)) = lines.next() {
        if let Ok(n) = line1.trim().parse::<usize>() {
            let mut u_edges = Vec::new();
            let mut v_edges = Vec::new();
            for _ in 0..(n - 1) {
                if let Some(Ok(line)) = lines.next() {
                    let parts: Vec<usize> = line.split_whitespace().filter_map(|s| s.parse().ok()).collect();
                    if parts.len() >= 2 {
                        u_edges.push(parts[0]);
                        v_edges.push(parts[1]);
                    }
                }
            }
            let (has_ans, center, leaves) = Solution::useful_decomposition(n, u_edges, v_edges);
            if !has_ans {
                println!("No");
            } else {
                println!("Yes");
                println!("{}", leaves.len());
                for leaf in leaves {
                    println!("{} {}", center, leaf);
                }
            }
        }
    }
}
