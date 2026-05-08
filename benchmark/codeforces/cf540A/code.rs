impl Solution {
    pub fn min_lock_moves(n: usize, current: Vec<u8>, target: Vec<u8>) -> u32 {
        let mut sum: u32 = 0;
        let mut i: usize = 0;
        while i < n {
            let ca = current[i] as u32;
            let cb = target[i] as u32;
            let d = if ca >= cb {
                ca - cb
            } else {
                cb - ca
            };
            let add = if d <= 5 {
                d
            } else {
                10 - d
            };
            sum = sum + add;
            i = i + 1;
        }
        sum
    }
}
