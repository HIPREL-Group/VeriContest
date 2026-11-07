impl Solution {
    pub fn find_array(pref: Vec<i32>) -> Vec<i32> {
        let n = pref.len();
        let mut result: Vec<i32> = Vec::new();
        result.push(pref[0]);
        let mut i: usize = 1;
        while i < n {
            let a = pref[i];
            let b = pref[i - 1];
            let val = a ^ b;
            result.push(val);
            i = i + 1;
        }
        result
    }
}
