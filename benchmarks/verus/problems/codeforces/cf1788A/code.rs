impl Solution {
    pub fn one_and_two(n: usize, a: Vec<i32>) -> i32 {
        let mut total: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            if a[i] == 2 {
                total = total + 1;
            }
            i = i + 1;
        }
        if total % 2 != 0 {
            return -1;
        }
        let target: i32 = total / 2;
        let mut twos: i32 = 0;
        let mut k: usize = 1;
        while k < n {
            if a[k - 1] == 2 {
                twos = twos + 1;
            }
            if twos == target {
                return k as i32;
            }
            k = k + 1;
        }
        -1
    }
}
