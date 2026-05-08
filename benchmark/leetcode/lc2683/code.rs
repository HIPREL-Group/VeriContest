impl Solution {
    fn xor_all_exec(derived: &Vec<i32>, idx: usize) -> i32 {
        let mut i: usize = idx;
        let mut acc: i32 = 0;
        while i < derived.len() {
            acc = acc ^ derived[i];
            i = i + 1;
        }
        acc
    }

    pub fn does_valid_array_exist(derived: Vec<i32>) -> bool {
        Self::xor_all_exec(&derived, 0) == 0
    }
}
