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

    pub fn generate(num_rows: i32) -> Vec<Vec<i32>> {
        let num_rows = num_rows as usize;
        let mut triangle = Vec::with_capacity(num_rows);
        triangle.push(vec![1]);
        while triangle.len() < num_rows {
            let last_n = triangle.len() - 1;
            triangle.push(Self::gen_next(&triangle[last_n]));
        }
        triangle
    }
}
