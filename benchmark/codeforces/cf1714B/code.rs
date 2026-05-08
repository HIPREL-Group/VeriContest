impl Solution {
    pub fn min_prefix_removals(n: usize, a: Vec<i32>) -> usize {
        let mut seen: Vec<bool> = Vec::new();
        let mut j: usize = 0;
        while j <= n {
            seen.push(false);
            j = j + 1;
        }
        let mut i: usize = n;
        while i > 0 {
            let x: usize = a[i - 1] as usize;
            if seen[x] {
                return i;
            }
            seen[x] = true;
            i = i - 1;
        }
        i
    }
}
