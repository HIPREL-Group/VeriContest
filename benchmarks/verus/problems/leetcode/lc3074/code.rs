impl Solution {
    pub fn minimum_boxes(apple: Vec<i32>, capacity: Vec<i32>) -> i32 {
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < apple.len() {
            total = total + apple[i] as i64;
            i = i + 1;
        }

        let mut need = total;
        let mut cap = capacity;
        let m = cap.len();
        let mut used: usize = 0;

        while used < m && need > 0 {
            let mut max_idx: usize = 0;
            let mut j: usize = 1;
            while j < m {
                if cap[j] >= cap[max_idx] {
                    max_idx = j;
                }
                j = j + 1;
            }

            need = need - cap[max_idx] as i64;
            cap[max_idx] = 0;
            used = used + 1;
        }

        used as i32
    }
}
