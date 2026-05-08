impl Solution {
    pub fn get_xor_sum(arr1: Vec<i32>, arr2: Vec<i32>) -> i32 {
        let mut xor1: i32 = 0;
        let mut i: usize = 0;
        while i < arr1.len() {
            xor1 = xor1 ^ arr1[i];
            i += 1;
        }
        let mut xor2: i32 = 0;
        let mut j: usize = 0;
        while j < arr2.len() {
            xor2 = xor2 ^ arr2[j];
            j += 1;
        }
        xor1 & xor2
    }
}
