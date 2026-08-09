fn merge_capped_exec(a: &Vec<i32>, b: &Vec<i32>, cap: usize) -> Vec<i32> {
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while result.len() < cap && (i < a.len() || j < b.len()) {
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

fn shift_exec(s: &Vec<i32>, shift: i32) -> Vec<i32> {
    let mut result: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < s.len() {
        result.push(s[idx] + shift);
        idx += 1;
    }
    result
}

fn fold_cols_exec(mat: &Vec<Vec<i32>>, row: usize, tail: &Vec<i32>, cap: usize) -> Vec<i32> {
    let n = mat[row].len();
    let mut acc: Vec<i32> = Vec::new();
    let mut c: usize = n;
    while c > 0 {
        c -= 1;
        let shifted = shift_exec(tail, mat[row][c]);
        acc = merge_capped_exec(&shifted, &acc, cap);
    }
    acc
}

fn capped_sums_exec(mat: &Vec<Vec<i32>>, cap: usize) -> Vec<i32> {
    let mut tail: Vec<i32> = Vec::new();
    if cap >= 1 {
        tail.push(0);
    }
    let m = mat.len();
    let mut row: usize = m;
    while row > 0 {
        row -= 1;
        tail = fold_cols_exec(mat, row, &tail, cap);
    }
    tail
}

impl Solution {
    pub fn kth_smallest(mat: Vec<Vec<i32>>, k: i32) -> i32 {
        let l = capped_sums_exec(&mat, k as usize);
        let ans = l[(k - 1) as usize];
        ans
    }
}
