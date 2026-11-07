fn merge_exec(a: &Vec<i64>, b: &Vec<i64>) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < a.len() || j < b.len() {
        if j >= b.len() || (i < a.len() && a[i] <= b[j]) {
            result.push(a[i]);
            i += 1;
        } else {
            result.push(b[j]);
            j += 1;
        }
    }
    result
}

fn merge_sort_exec(v: &Vec<i64>) -> Vec<i64> {
    if v.len() <= 1 {
        let mut result: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < v.len() {
            result.push(v[k]);
            k += 1;
        }
        result
    } else {
        let mid = v.len() / 2;
        let mut left: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < mid {
            left.push(v[i]);
            i += 1;
        }
        let mut right: Vec<i64> = Vec::new();
        let mut i2: usize = mid;
        while i2 < v.len() {
            right.push(v[i2]);
            i2 += 1;
        }
        let sorted_left = merge_sort_exec(&left);
        let sorted_right = merge_sort_exec(&right);
        let result = merge_exec(&sorted_left, &sorted_right);
        result
    }
}

fn encode_exec(v: i32, i: usize) -> i64 {
    (v as i64) * 200000 + (i as i64)
}

fn decode_idx_exec(e: i64) -> i64 {
    e % 200000
}

impl Solution {
    pub fn unmarked_sum_array(nums: Vec<i32>, queries: Vec<Vec<i32>>) -> Vec<i64> {
        let n = nums.len();

        let mut enc: Vec<i64> = Vec::new();
        let mut ii: usize = 0;
        while ii < n {
            let e = encode_exec(nums[ii], ii);
            enc.push(e);
            ii += 1;
        }
        let sorted = merge_sort_exec(&enc);

        let mut marked: Vec<bool> = Vec::new();
        let mut jj: usize = 0;
        while jj < n {
            marked.push(false);
            jj += 1;
        }

        let mut total: i64 = 0;
        let mut pp: usize = 0;
        while pp < n {
            total = total + nums[pp] as i64;
            pp += 1;
        }
        let mut unmarked_sum: i64 = total;

        let mut ptr: usize = 0;
        let mut result: Vec<i64> = Vec::new();
        let mut q: usize = 0;
        while q < queries.len() {
            let idx = queries[q][0] as usize;
            let k = queries[q][1];
            if !marked[idx] {
                marked[idx] = true;
                unmarked_sum = unmarked_sum - nums[idx] as i64;
            }

            let mut t: i32 = 0;
            while t < k && ptr < n {
                let mut cont: bool = false;
                if ptr < n {
                    let sp = sorted[ptr];
                    let di = decode_idx_exec(sp);
                    cont = marked[di as usize];
                }
                while cont {
                    ptr += 1;
                    cont = false;
                    if ptr < n {
                        let sp = sorted[ptr];
                        let di = decode_idx_exec(sp);
                        cont = marked[di as usize];
                    }
                }
                if ptr < n {
                    let sp2 = sorted[ptr];
                    let di2 = decode_idx_exec(sp2);
                    let target = di2 as usize;
                    marked[target] = true;
                    unmarked_sum = unmarked_sum - nums[target] as i64;
                    ptr += 1;
                }
                t += 1;
            }

            result.push(unmarked_sum);
            q += 1;
        }

        result
    }
}
