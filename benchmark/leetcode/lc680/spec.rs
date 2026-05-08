use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn measure(i: int, j: int) -> nat {
        if j >= i { (j - i) as nat } else { 0 }
    }

    pub open spec fn is_palindrome(s: Seq<char>, start: int, end: int) -> bool {
        forall |k: int| 0 <= k && k <= (end - start) / 2 ==> #[trigger] s[start + k] == s[end - k]
    }

    pub open spec fn valid_palindrome_rec(s: Seq<char>, i: int, j: int) -> bool
        decreases Solution::measure(i, j)
    {
        if i >= j {
            true
        } else if s[i] == s[j] {
            Solution::valid_palindrome_rec(s, i + 1, j - 1)
        } else {
            Solution::is_palindrome(s, i + 1, j) || Solution::is_palindrome(s, i, j - 1)
        }
    }

    pub open spec fn valid_palindrome_spec(s: Seq<char>) -> bool {
        Solution::valid_palindrome_rec(s, 0, s.len() as int - 1)
    }

    pub fn check_palindrome(s: &Vec<char>, start: usize, end: usize) -> (res: bool)
        requires
            start <= s.len(),
            end < s.len(),
            start <= end + 1,
        ensures
            res == Solution::is_palindrome(s@, start as int, end as int),
    {

    }

    pub fn valid_palindrome(s: Vec<char>) -> (res: bool)
        requires
            1 <= s.len() <= 100000,
        ensures
            res == Solution::valid_palindrome_spec(s@),
    {

    }
}

} 
