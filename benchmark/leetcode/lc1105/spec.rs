use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
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
    }
}

}
