impl Solution {
    pub fn co_growing(n: usize, x: Vec<u32>) -> Vec<u32> {
        let mut y: Vec<u32> = Vec::new();
        let mut z: u32 = x[0];
        let y0 = z ^ x[0];
        y.push(y0);
        let mut i: usize = 1;
        while i < n {
            let old_z = z;
            z = z | x[i];
            let yi = z ^ x[i];
            y.push(yi);
            i += 1;
        }
        y
    }
}
