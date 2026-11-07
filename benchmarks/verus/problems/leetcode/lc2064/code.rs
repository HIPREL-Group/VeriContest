impl Solution {
    fn stores_needed_exec(quantities: &Vec<i32>, x: i32) -> i64 {
        let mut need: i64 = 0;
        let mut i: usize = 0;
        while i < quantities.len() {
            let q = quantities[i];
            let add: i64 = (q as i64 + x as i64 - 1) / x as i64;
            need = need + add;
            i = i + 1;
        }
        need
    }

    pub fn minimized_maximum(n: i32, quantities: Vec<i32>) -> i32 {
        let mut left: i32 = 1;
        let mut right: i32 = 100000;
        while left < right {
            let mid = left + (right - left) / 2;
            let need = Self::stores_needed_exec(&quantities, mid);
            if need <= n as i64 {
                right = mid;
            } else {
                left = mid + 1;
            }
        }
        left
    }
}
