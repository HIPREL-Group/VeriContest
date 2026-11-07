use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn detect_capital_use(word: String) -> (res: bool) 
        requires
            1 <= word@.len() <= 100,
            forall |i: int| 0 <= i < word@.len() ==> 
                (('A' <= word@[i] && word@[i] <= 'Z') || ('a' <= word@[i] && word@[i] <= 'z')),
        ensures
            res == (
                (forall |i: int| 0 <= i < word@.len() ==> ('A' <= word@[i] && word@[i] <= 'Z')) ||
                (forall |i: int| 0 <= i < word@.len() ==> ('a' <= word@[i] && word@[i] <= 'z')) ||
                (('A' <= word@[0] && word@[0] <= 'Z') && 
                 forall |i: int| 1 <= i < word@.len() ==> ('a' <= word@[i] && word@[i] <= 'z'))
            ),
    {
        
    }
}

}