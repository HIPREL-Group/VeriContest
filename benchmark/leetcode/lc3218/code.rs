impl Solution {
    pub fn minimum_cost(m: i32, n: i32, horizontal_cut: Vec<i32>, vertical_cut: Vec<i32>) -> i32 {
        let hm = horizontal_cut.len();
        let vn = vertical_cut.len();
        let mut res = 0i32;

        let mut i = 0usize;
        while i < hm {
            res = res.checked_add(horizontal_cut[i]).unwrap_or(res);
            i += 1;
        }

        let mut j = 0usize;
        while j < vn {
            res = res.checked_add(vertical_cut[j]).unwrap_or(res);
            j += 1;
        }

        let mut a = 0usize;
        while a < hm {
            let mut b = 0usize;
            while b < vn {
                let add = if horizontal_cut[a] <= vertical_cut[b] { horizontal_cut[a] } else { vertical_cut[b] };
                res = res.checked_add(add).unwrap_or(res);
                b += 1;
            }
            a += 1;
        }

        if res < 0 { 0 } else { res }
    }
}
