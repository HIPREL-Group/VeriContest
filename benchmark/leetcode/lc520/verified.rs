use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
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
        let len = word.as_str().unicode_len();
        
        let mut all_upper = true;
        let mut i: usize = 0;
        while i < len && all_upper
            invariant
                1 <= word@.len() <= 100,
                len == word@.len(),
                forall |i: int| 0 <= i < word@.len() ==> 
                    (('A' <= word@[i] && word@[i] <= 'Z') || ('a' <= word@[i] && word@[i] <= 'z')),
                0 <= i <= len,
                all_upper ==> forall |j: int| 0 <= j < i ==> ('A' <= word@[j] && word@[j] <= 'Z'),
                !all_upper ==> exists |j: int| 0 <= j < i && !('A' <= word@[j] && word@[j] <= 'Z'),
        {
            let c = word.as_str().get_char(i);
            if !(c >= 'A' && c <= 'Z') {
                all_upper = false;
            }
            i += 1;
        }
        
        if all_upper {
            return true;
        }
        
        let mut all_lower = true;
        i = 0;
        while i < len && all_lower
            invariant
                1 <= word@.len() <= 100,
                len == word@.len(),
                forall |i: int| 0 <= i < word@.len() ==> 
                    (('A' <= word@[i] && word@[i] <= 'Z') || ('a' <= word@[i] && word@[i] <= 'z')),
                0 <= i <= len,
                all_lower ==> forall |j: int| 0 <= j < i ==> ('a' <= word@[j] && word@[j] <= 'z'),
                !all_lower ==> exists |j: int| 0 <= j < i && !('a' <= word@[j] && word@[j] <= 'z'),
        {
            let c = word.as_str().get_char(i);
            if !(c >= 'a' && c <= 'z') {
                all_lower = false;
            }
            i += 1;
        }
        
        if all_lower {
            return true;
        }
        
        let first = word.as_str().get_char(0);
        if !(first >= 'A' && first <= 'Z') {
            return false;
        }
                
        i = 1;
        let mut rest_lower = true;
        while i < len && rest_lower
            invariant
                1 <= word@.len() <= 100,
                len == word@.len(),
                forall |i: int| 0 <= i < word@.len() ==> 
                    (('A' <= word@[i] && word@[i] <= 'Z') || ('a' <= word@[i] && word@[i] <= 'z')),
                'A' <= word@[0] && word@[0] <= 'Z',
                1 <= i <= len,
                rest_lower ==> forall |j: int| 1 <= j < i ==> ('a' <= word@[j] && word@[j] <= 'z'),
                !rest_lower ==> exists |j: int| 1 <= j < i && !('a' <= word@[j] && word@[j] <= 'z'),
        {
            let c = word.as_str().get_char(i);
            if !(c >= 'a' && c <= 'z') {
                rest_lower = false;
            }
            i += 1;
        }
        
        rest_lower
    }
}

}