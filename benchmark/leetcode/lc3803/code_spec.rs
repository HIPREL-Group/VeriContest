use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_lowercase_string(s: Seq<char>) -> bool {
        forall |i: int| 0 <= i < s.len() ==> 97 <= (#[trigger] s[i] as u32) && (s[i] as u32) <= 122
    }

    pub open spec fn is_first_occurrence(s: Seq<char>, idx: nat) -> bool
        recommends
            idx < s.len(),
    {
        forall |q: int| 0 <= q < idx ==> s[q] != s[idx as int]
    }

    pub open spec fn distinct_count_prefix(s: Seq<char>, n: nat) -> int
        recommends
            n <= s.len(),
        decreases n,
    {
        if n == 0 {
            0
        } else {
            Self::distinct_count_prefix(s, (n - 1) as nat)
                + (if Self::is_first_occurrence(s, (n - 1) as nat) { 1int } else { 0int })
        }
    }

    pub open spec fn residue_prefix_count(s: Seq<char>, n: nat) -> int
        recommends
            n <= s.len(),
        decreases n,
    {
        if n == 0 {
            0
        } else {
            Self::residue_prefix_count(s, (n - 1) as nat)
                + (if Self::distinct_count_prefix(s, n) == (n as int) % 3 { 1int } else { 0int })
        }
    }

    fn is_first_at(s: &String, p: usize) -> (res: bool)
        requires
            p < s@.len(),
    {
        let mut q: usize = 0;
        while q < p {
            if s.as_str().get_char(q) == s.as_str().get_char(p) {
                return false;
            }
            q += 1;
        }
        true
    }

    pub fn residue_prefixes(s: String) -> (res: i32)
        requires
            1 <= s@.len() <= 100,
            Self::is_lowercase_string(s@),
        ensures
            res as int == Self::residue_prefix_count(s@, s@.len()),
    {
        let n = s.as_str().unicode_len();
        let mut ans: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            let mut distinct: i32 = 0;
            let mut p: usize = 0;
            while p <= i {
                let is_new = Self::is_first_at(&s, p);
                if is_new {
                    distinct += 1;
                }
                p += 1;
            }

            let residue: i32 = ((i + 1) % 3) as i32;
            if distinct == residue {
                ans += 1;
            }
            i += 1;
        }
        ans
    }
}

}
