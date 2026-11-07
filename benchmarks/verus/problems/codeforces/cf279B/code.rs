impl Solution {
    pub fn max_books_read(books: Vec<i32>, t: i64) -> usize {
        let n = books.len();
        let mut left: usize = 0;
        let mut right: usize = 0;
        let mut sum: i64 = 0;
        let mut best: usize = 0;
        while right < n {
            sum = sum + books[right] as i64;
            right += 1;
            while sum > t && left < right {
                sum = sum - books[left] as i64;
                left += 1;
            }
            if right - left > best {
                best = right - left;
            }
        }
        best
    }
}
