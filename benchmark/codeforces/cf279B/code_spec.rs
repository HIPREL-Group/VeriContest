use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn segment_sum(s: Seq<i32>, start: int, len: int) -> int
    decreases len,
{
    if len <= 0 {
        0
    } else {
        s[start] as int + segment_sum(s, start + 1, len - 1)
    }
}

pub open spec fn segment_fits(books: Seq<i32>, start: int, len: int, t: int) -> bool
    recommends 0 <= start, 0 <= len, start + len <= books.len(),
{
    segment_sum(books, start, len) <= t
}

pub open spec fn any_segment_of_len_fits(books: Seq<i32>, len: int, t: int) -> bool
    recommends 0 <= len <= books.len(),
{
    exists|i: int| 0 <= i && i + len <= books.len() && segment_fits(books, i, len, t)
}

impl Solution {
    pub fn max_books_read(books: Vec<i32>, t: i64) -> (result: usize)
        requires
            1 <= books.len() <= 100_000,
            1 <= t <= 1_000_000_000,
            forall|i: int| 0 <= i < books@.len() ==> 1 <= #[trigger] books@[i] <= 10_000,
        ensures
            (result as int) <= books@.len(),
            0 <= (result as int),
            exists|i: int|
                0 <= i && i + (result as int) <= books@.len()
                    && segment_fits(books@, i, result as int, t as int),
            forall|k: int|
                (result as int) < k && k <= books@.len() ==> !#[trigger] any_segment_of_len_fits(books@, k, t as int),
    {
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

}
