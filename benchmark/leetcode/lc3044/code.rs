impl Solution {
    fn get_dx(d: usize) -> i32 {
        if d == 0 { 0 } else if d == 1 { 1 } else if d == 2 { 1 } else if d == 3 { 1 }
        else if d == 4 { 0 } else if d == 5 { -1 } else if d == 6 { -1 } else { -1 }
    }

    fn get_dy(d: usize) -> i32 {
        if d == 0 { 1 } else if d == 1 { 1 } else if d == 2 { 0 } else if d == 3 { -1 }
        else if d == 4 { -1 } else if d == 5 { -1 } else if d == 6 { 0 } else { 1 }
    }

    fn is_prime(num: i32) -> bool {
        if num <= 1 {
            return false;
        }
        let mut d = 2;
        while d * d <= num {
            if num % d == 0 {
                return false;
            }
            d += 1;
        }
        true
    }

    pub fn most_frequent_prime(mat: Vec<Vec<i32>>) -> i32 {
        let m = mat.len();
        let n = mat[0].len();
        let total = m * n;

        let mut nums: Vec<i32> = Vec::new();
        let mut idx = 0;
        while idx < total {
            let r = idx / n;
            let c = idx % n;
            let mut d = 0;
            while d < 8 {
                let mut rr = r as i32;
                let mut cc = c as i32;
                let mut cur = mat[r][c];
                let mut active = true;
                let mut step = 1;
                while step <= 5 {
                    let dx_d = Self::get_dx(d);
                    let dy_d = Self::get_dy(d);
                    rr += dx_d;
                    cc += dy_d;
                    if active && 0 <= rr && rr < m as i32 && 0 <= cc && cc < n as i32 {
                        cur = cur * 10 + mat[rr as usize][cc as usize];
                        nums.push(cur);
                    } else {
                        active = false;
                    }
                    step += 1;
                }
                d += 1;
            }
            idx += 1;
        }

        let mut best = -1;
        let mut best_count: i32 = 0;
        let mut i = 0;
        while i < nums.len() {
            let val = nums[i];
            if val > 10 && Self::is_prime(val) {
                let mut count: i32 = 0;
                let mut j = 0;
                while j < nums.len() {
                    if nums[j] == val {
                        count += 1;
                    }
                    j += 1;
                }
                if count > best_count || (count == best_count && val > best) {
                    best_count = count;
                    best = val;
                }
            }
            i += 1;
        }

        best
    }
}
