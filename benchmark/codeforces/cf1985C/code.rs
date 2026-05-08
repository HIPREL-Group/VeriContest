impl Solution {
    pub fn count_good_prefixes_fn(a: Vec<u64>) -> usize {
        let mut sum: u64 = 0;
        let mut max_val: u64 = 0;
        let mut count: usize = 0;
        let mut i: usize = 0;
        while i < a.len() {
            let ai = a[i];
            sum = sum + ai;
            if ai > max_val {
                max_val = ai;
            }
            if 2 * max_val == sum {
                count = count + 1;
            }
            i = i + 1;
        }
        count
    }
}
