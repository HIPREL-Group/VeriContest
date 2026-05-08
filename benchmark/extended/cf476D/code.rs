impl Solution {
    pub fn build_dreamoon_sets(n: usize, k: i32) -> Vec<Vec<i32>> {
        let mut sets: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let base = 6 * (i as i64);
            let v0 = ((k as i64) * (base + 1)) as i32;
            let v1 = ((k as i64) * (base + 2)) as i32;
            let v2 = ((k as i64) * (base + 3)) as i32;
            let v3 = ((k as i64) * (base + 5)) as i32;
            let mut row: Vec<i32> = Vec::new();
            row.push(v0);
            row.push(v1);
            row.push(v2);
            row.push(v3);
            sets.push(row);
            i = i + 1;
        }
        sets
    }
}
