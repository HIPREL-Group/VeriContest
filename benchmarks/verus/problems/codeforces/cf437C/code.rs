impl Solution {
    pub fn min_total_energy(weights: Vec<i64>, edges: Vec<(usize, usize)>) -> i64 {
        let mut total = 0i64;
        let mut i = 0usize;
        while i < edges.len() {
            let u = edges[i].0;
            let v = edges[i].1;
            let wu = weights[u];
            let wv = weights[v];
            let add = if wu <= wv { wu } else { wv };
            total += add;
            i += 1;
        }
        total
    }
}
