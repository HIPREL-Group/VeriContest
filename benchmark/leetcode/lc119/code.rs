impl Solution {
    pub fn gen_next(last: &Vec<i32>) -> Vec<i32> {
        let mut i = 1;
        let mut ret = Vec::with_capacity(last.len() + 1);
        ret.push(last[0]);
        while i < last.len() {
            ret.push(last[i - 1] + last[i]);
            i += 1;
        }
        ret.push(last[last.len() - 1]);
        ret
    }

    pub fn get_row(row_index: i32) -> Vec<i32> {
        let mut i = 0;
        let mut row = vec![1];
        while i != row_index {
            row = Self::gen_next(&row);
            i += 1;
        }
        row
    }
}
