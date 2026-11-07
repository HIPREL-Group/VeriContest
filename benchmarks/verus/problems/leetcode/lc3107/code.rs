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

fn decode_val_exec(e: i64) -> i64 {
    e / 200000
}

impl Solution {
    pub fn min_operations_to_make_median_k(nums: Vec<i32>, k: i32) -> i64 {
        let n = nums.len();

        let mut enc: Vec<i64> = Vec::new();
        let mut ii: usize = 0;
        while ii < n {
            let e = encode_exec(nums[ii], ii);
            enc.push(e);
            ii += 1;
        }

        let sorted = merge_sort_exec(&enc);

        let mut a: Vec<i32> = Vec::new();
        let mut pp: usize = 0;
        while pp < n {
            let dv = decode_val_exec(sorted[pp]);
            let v32 = dv as i32;
            a.push(v32);
            pp += 1;
        }

        let mid = n / 2;
        let mut ans: i128 = 0;
        let mut idx: usize = 0;
        while idx < n {
            let v = a[idx];
            if idx < mid {
                if v > k {
                    let d = v - k;
                    ans = ans + d as i128;
                }
            } else if idx == mid {
                if v >= k {
                    let d = v - k;
                    ans = ans + d as i128;
                } else {
                    let d = k - v;
                    ans = ans + d as i128;
                }
            } else {
                if v < k {
                    let d = k - v;
                    ans = ans + d as i128;
                }
            }
            idx = idx + 1;
        }

        ans as i64
    }
}
