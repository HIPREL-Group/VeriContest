impl Solution {
    pub fn not_dividing_array(a: Vec<i32>) -> Vec<i32> {
        let n = a.len();
        let mut v = a;
        let mut i: usize = 0;
        while i < n {
            if v[i] == 1 {
                v[i] = 2;
            }
            i = i + 1;
        }
        let mut j: usize = 0;
        while j + 1 < n {
            let vj = v[j];
            let vj1 = v[j + 1];
            if vj1 % vj == 0 {
                let vj1_next: i32 = vj1 + 1;
                v[j + 1] = vj1_next;
            }
            j = j + 1;
        }
        v
    }
}
