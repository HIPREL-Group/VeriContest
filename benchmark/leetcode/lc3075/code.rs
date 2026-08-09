fn merge_exec_desc(a: &Vec<i32>, b: &Vec<i32>) -> Vec<i32> {
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < a.len() || j < b.len() {
        if j >= b.len() || (i < a.len() && a[i] >= b[j]) {
            result.push(a[i]);
            i += 1;
        } else {
            result.push(b[j]);
            j += 1;
        }
    }
    result
}

fn merge_sort_exec_desc(v: &Vec<i32>) -> Vec<i32> {
    if v.len() <= 1 {
        v.clone()
    } else {
        let mid = v.len() / 2;
        let mut left: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < mid {
            left.push(v[i]);
            i += 1;
        }
        let mut right: Vec<i32> = Vec::new();
        let mut i2: usize = mid;
        while i2 < v.len() {
            right.push(v[i2]);
            i2 += 1;
        }
        let sorted_left = merge_sort_exec_desc(&left);
        let sorted_right = merge_sort_exec_desc(&right);
        let result = merge_exec_desc(&sorted_left, &sorted_right);
        result
    }
}

impl Solution {
    pub fn maximum_happiness_sum(happiness: Vec<i32>, k: i32) -> i64 {
        let sorted = merge_sort_exec_desc(&happiness);
        let mut ans: i64 = 0;
        let mut i: usize = 0;
        let ku = k as usize;
        while i < ku {
            let v = sorted[i] as i64;
            let gain = v - i as i64;
            if gain > 0 {
                ans = ans + gain;
            }
            i += 1;
        }
        ans
    }
}
