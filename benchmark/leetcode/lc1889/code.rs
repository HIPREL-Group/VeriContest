fn merge_exec(a: &Vec<i32>, b: &Vec<i32>) -> Vec<i32> {
    let mut result: Vec<i32> = Vec::new();
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

fn merge_sort_exec(v: &Vec<i32>) -> Vec<i32> {
    if v.len() <= 1 {
        let mut result: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < v.len() {
            result.push(v[k]);
            k += 1;
        }
        result
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
        let sorted_left = merge_sort_exec(&left);
        let sorted_right = merge_sort_exec(&right);
        let result = merge_exec(&sorted_left, &sorted_right);
        result
    }
}

impl Solution {
    pub fn min_wasted_space(packages: Vec<i32>, boxes: Vec<Vec<i32>>) -> i32 {
        let n = packages.len();
        let m = boxes.len();
        let modulo: i64 = 1_000_000_007;

        let mut pkg_count: Vec<i64> = Vec::new();
        let mut vi: usize = 0;
        while vi <= 100_000 {
            pkg_count.push(0);
            vi += 1;
        }

        let mut i: usize = 0;
        while i < n {
            let val = packages[i] as usize;
            pkg_count[val] = pkg_count[val] + 1;
            i += 1;
        }

        let mut pkg_count_prefix: Vec<i64> = Vec::new();
        pkg_count_prefix.push(pkg_count[0]);
        let mut pkg_sum_prefix: Vec<i64> = Vec::new();
        pkg_sum_prefix.push(0);
        let mut v1: usize = 1;
        while v1 <= 100_000 {
            let next_count = pkg_count_prefix[v1 - 1] + pkg_count[v1];
            pkg_count_prefix.push(next_count);
            let next_sum = pkg_sum_prefix[v1 - 1] + (v1 as i64) * pkg_count[v1];
            pkg_sum_prefix.push(next_sum);
            v1 += 1;
        }

        let mut best: i64 = -1;
        let mut j: usize = 0;
        while j < m {
            let sorted_bj = merge_sort_exec(&boxes[j]);
            let bj_len = sorted_bj.len();
            let mut waste: i64 = 0;
            let mut prev: usize = 0;
            let mut t: usize = 0;
            while t < bj_len {
                let b = sorted_bj[t];
                let bu = b as usize;
                let cnt = pkg_count_prefix[bu] - pkg_count_prefix[prev];
                let sm = pkg_sum_prefix[bu] - pkg_sum_prefix[prev];
                waste = waste + (bu as i64) * cnt - sm;
                prev = bu;
                t += 1;
            }
            let remaining = pkg_count_prefix[100_000] - pkg_count_prefix[prev];
            let can_fit = remaining == 0;
            if can_fit {
                if best == -1 || waste < best {
                    best = waste;
                }
            }
            j += 1;
        }

        if best == -1 {
            -1
        } else {
            (best % modulo) as i32
        }
    }
}
