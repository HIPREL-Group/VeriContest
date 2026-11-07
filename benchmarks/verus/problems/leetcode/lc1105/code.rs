impl Solution {
    pub fn min_height_shelves(books: Vec<Vec<i32>>, shelf_width: i32) -> i32 {
        let n = books.len();
        let mut dp: Vec<i32> = Vec::new();
        dp.push(0);
        let mut i: usize = 1;
        while i <= n {
            let mut width: i32 = 0;
            let mut height: i32 = 0;
            let mut best: i32 = 1_000_001;
            let mut j: usize = i;
            let mut stopped: bool = false;
            while j > 0 && !stopped {
                let book_thickness = books[j - 1][0];
                let book_height = books[j - 1][1];
                let next_width = width + book_thickness;
                if next_width > shelf_width {
                    stopped = true;
                } else {
                    j = j - 1;
                    width = next_width;
                    let new_height = if book_height > height { book_height } else { height };
                    let candidate = dp[j] + new_height;
                    if candidate < best {
                        best = candidate;
                    }
                    height = new_height;
                }
            }
            dp.push(best);
            i = i + 1;
        }
        dp[n]
    }
}
