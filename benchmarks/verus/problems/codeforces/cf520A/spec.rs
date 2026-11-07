use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn valid_latin(c: u8) -> bool {
    (c >= 65u8 && c <= 90u8) || (c >= 97u8 && c <= 122u8)
}

pub open spec fn letter_index(c: u8) -> int {
    if c >= 65u8 && c <= 90u8 {
        (c - 65u8) as int
    } else {
        (c - 97u8) as int
    }
}

pub open spec fn covered_through(s: Seq<u8>, i: int, k: int) -> bool {
    exists|j: int|
        0 <= j && j < i && letter_index(#[trigger] s[j]) == k
}

pub open spec fn spec_is_pangram(s: Seq<u8>) -> bool {
    forall|k: int|
        0 <= k < 26 ==> #[trigger] covered_through(s, s.len() as int, k)
}

impl Solution {
    pub fn is_pangram(n: usize, s: Vec<u8>) -> (res: bool)
        requires
            1 <= n <= 100,
            n == s.len(),
            forall|u: int|
                0 <= u < n as int ==> valid_latin(#[trigger] s[u]),
        ensures
            res == spec_is_pangram(s@),
    {
    }
}

}
