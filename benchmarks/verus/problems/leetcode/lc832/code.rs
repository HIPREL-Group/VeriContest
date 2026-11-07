impl Solution {
    pub fn flip_and_invert_image(image: Vec<Vec<i32>>) -> Vec<Vec<i32>> {
        let n = image.len();
        let mut result: Vec<Vec<i32>> = Vec::new();

        let mut i: usize = 0;
        while i < n {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                row.push(1 - image[i][n - 1 - j]);
                j += 1;
            }
            result.push(row);
            i += 1;
        }

        result
    }
}
