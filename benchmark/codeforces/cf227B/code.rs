impl Solution {
    pub fn effective_approach(permutation: Vec<i32>, queries: Vec<i32>) -> (i64, i64) {
        let n = permutation.len();
        let mut positions = Vec::new();
        let mut t = 0usize;
        while t <= n {
            positions.push(0i64);
            t += 1;
        }
        let mut i = 0usize;
        while i < n {
            let value = permutation[i] as usize;
            positions[value] = i as i64 + 1;
            i += 1;
        }
        let mut vasya = 0i64;
        let mut petya = 0i64;
        let mut j = 0usize;
        while j < queries.len() {
            let value = queries[j] as usize;
            let p = positions[value];
            vasya += p;
            petya += n as i64 - p + 1;
            j += 1;
        }
        (vasya, petya)
    }
}
