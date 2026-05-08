use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min2(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn max2(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    
    pub open spec fn shelf_total_width(books: Seq<Vec<i32>>, start: int, end: int) -> int
        decreases end - start,
    {
        if start >= end { 0 }
        else { books[start][0] as int + Self::shelf_total_width(books, start + 1, end) }
    }

    
    pub open spec fn shelf_max_height(books: Seq<Vec<i32>>, start: int, end: int) -> int
        decreases end - start,
    {
        if start >= end { 0 }
        else { Self::max2(books[start][1] as int, Self::shelf_max_height(books, start + 1, end)) }
    }

    
    
    pub open spec fn is_valid_arrangement(books: Seq<Vec<i32>>, n: int, cuts: Seq<int>, shelf_width: int) -> bool {
        cuts.len() >= 1
        && cuts[0] == 0
        && cuts[cuts.len() - 1] == n
        && (forall |k: int| 0 <= k < cuts.len() - 1 ==>
            (#[trigger] cuts[k]) < cuts[k + 1]
            && Self::shelf_total_width(books, cuts[k], cuts[k + 1]) <= shelf_width)
    }

    
    pub open spec fn arrangement_height(books: Seq<Vec<i32>>, cuts: Seq<int>) -> int
        decreases cuts.len(),
    {
        if cuts.len() <= 1 { 0 }
        else {
            let k = (cuts.len() - 1) as int;
            Self::arrangement_height(books, cuts.take(k)) + Self::shelf_max_height(books, cuts[k - 1], cuts[k])
        }
    }

    pub open spec fn min_height_dp(books: Seq<Vec<i32>>, sw: int, i: int) -> int
        decreases i + 1, 0int,
    {
        if i <= 0 {
            0
        } else {
            Self::best_shelf(books, sw, i, i - 1, 0, 0)
        }
    }

    pub open spec fn best_shelf(books: Seq<Vec<i32>>, sw: int, i: int, j: int, width: int, height: int) -> int
        recommends
            0 <= j < i <= books.len(),
        decreases j + 1, 1int,
    {
        let new_width = width + books[j][0] as int;
        let new_height = Self::max2(height, books[j][1] as int);
        if new_width > sw {
            1_000_001
        } else {
            let candidate = Self::min_height_dp(books, sw, j) + new_height;
            if j <= 0 {
                candidate
            } else {
                Self::min2(candidate, Self::best_shelf(books, sw, i, j - 1, new_width, new_height))
            }
        }
    }

    pub fn min_height_shelves(books: Vec<Vec<i32>>, shelf_width: i32) -> (res: i32)
        requires
            1 <= books.len() <= 1000,
            1 <= shelf_width <= 1000,
            forall |i: int| 0 <= i < books.len() ==> #[trigger] books[i].len() == 2,
            forall |i: int| 0 <= i < books.len() ==> 1 <= #[trigger] books[i][0] <= shelf_width,
            forall |i: int| 0 <= i < books.len() ==> 1 <= #[trigger] books[i][1] <= 1000,
        ensures
            exists |cuts: Seq<int>| #[trigger] Self::is_valid_arrangement(books@, books.len() as int, cuts, shelf_width as int)
                && Self::arrangement_height(books@, cuts) == res as int,
            forall |cuts: Seq<int>| Self::is_valid_arrangement(books@, books.len() as int, cuts, shelf_width as int)
                ==> res as int <= #[trigger] Self::arrangement_height(books@, cuts),
    {
        let n = books.len();
        let sw = shelf_width;
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
                    let old_best = best;
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

}
