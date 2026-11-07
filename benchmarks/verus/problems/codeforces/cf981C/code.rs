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
