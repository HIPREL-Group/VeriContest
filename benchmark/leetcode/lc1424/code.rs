impl Solution {
    pub fn find_diagonal_order(nums: Vec<Vec<i32>>) -> Vec<i32> {
        let m = nums.len();

        let mut max_d: usize = 0;
        let mut i: usize = m;
        while i > 0 {
            i = i - 1;
            let d = i + nums[i].len() - 1;
            if d > max_d {
                max_d = d;
            }
        }

        let mut count: Vec<usize> = Vec::new();
        let mut k: usize = 0;
        while k <= max_d {
            count.push(0);
            k = k + 1;
        }

        let mut i2: usize = 0;
        while i2 < m {
            let row_len = nums[i2].len();
            let mut j: usize = 0;
            while j < row_len {
                let d = i2 + j;
                count[d] = count[d] + 1;
                j = j + 1;
            }
            i2 = i2 + 1;
        }

        let mut offset: Vec<usize> = Vec::new();
        offset.push(0);
        let mut k2: usize = 0;
        while k2 <= max_d {
            let next = offset[k2] + count[k2];
            offset.push(next);
            k2 = k2 + 1;
        }

        let total = offset[max_d + 1];

        let mut result: Vec<i32> = Vec::new();
        let mut z: usize = 0;
        while z < total {
            result.push(0);
            z = z + 1;
        }

        let mut cursor: Vec<usize> = Vec::new();
        let mut k3: usize = 0;
        while k3 <= max_d {
            cursor.push(offset[k3 + 1]);
            k3 = k3 + 1;
        }

        let mut i3: usize = 0;
        while i3 < m {
            let row_len3 = nums[i3].len();
            let mut j3: usize = 0;
            while j3 < row_len3 {
                let d = i3 + j3;
                let old_cursor_d = cursor[d];
                cursor[d] = cursor[d] - 1;
                let val = nums[i3][j3];
                result[cursor[d]] = val;
                j3 = j3 + 1;
            }
            i3 = i3 + 1;
        }

        result
    }
}
