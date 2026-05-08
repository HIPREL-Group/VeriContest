impl Solution {
    pub fn optimal_permutation(n: i32) -> Vec<i32> {
        let mut p: Vec<i32> = Vec::new();
        let h = n / 2;
        let mut i = 1;
        while i <= h {
            p.push(h + i);
            p.push(i);
            i = i + 1;
        }
        if n % 2 == 1 {
            p.push(n);
        }
        p
    }
}
