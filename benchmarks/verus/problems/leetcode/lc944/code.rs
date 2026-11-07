impl Solution {
    pub fn min_deletion_size(strs: Vec<String>) -> i32 {
        let rows = strs.len();
        let cols = strs[0].as_str().unicode_len();
        let mut deleted = 0;
        let mut col: usize = 0;

        while col < cols {
            let mut bad = false;
            let mut row: usize = 1;
            while row < rows {
                if strs[row - 1].as_str().get_char(col) > strs[row].as_str().get_char(col) {
                    bad = true;
                }
                row += 1;
            }
            if bad {
                deleted += 1;
            }
            col += 1;
        }

        deleted
    }
}
