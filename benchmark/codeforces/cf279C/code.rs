impl Solution {
    pub fn query_ladders(arr: Vec<i64>, queries: Vec<(i32, i32)>) -> Vec<bool> {
        let n = arr.len();
        let mut up_end = Vec::new();
        let mut i = 0usize;
        while i < n {
            up_end.push(0usize);
            i = i + 1;
        }
        up_end[n - 1] = n - 1;
        i = n - 1;
        while i > 0 {
            let j = i - 1;
            if arr[j] <= arr[j + 1] {
                up_end[j] = up_end[j + 1];
            } else {
                up_end[j] = j;
            }
            i = j;
        }
        let mut down_end = Vec::new();
        i = 0;
        while i < n {
            down_end.push(0usize);
            i = i + 1;
        }
        down_end[n - 1] = n - 1;
        i = n - 1;
        while i > 0 {
            let j = i - 1;
            if arr[j] >= arr[j + 1] {
                down_end[j] = down_end[j + 1];
            } else {
                down_end[j] = j;
            }
            i = j;
        }
        let mut res = Vec::new();
        let mut qi = 0usize;
        while qi < queries.len() {
            let (l1, r1) = queries[qi];
            let l = (l1 - 1) as usize;
            let r = (r1 - 1) as usize;
            let peak = up_end[l];
            let answer = down_end[peak] >= r;
            res.push(answer);
            qi = qi + 1;
        }
        res
    }
}
