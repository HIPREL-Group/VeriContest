impl Solution {
    pub fn check_palindrome(s: &Vec<char>, start: usize, end: usize) -> bool {
        if start >= end {
            return true;
        }

        let mut i = start;
        let mut j = end;

        while i < j {
            if s[i] != s[j] {
                return false;
            }
            i += 1;
            j -= 1;
        }

        true
    }

    pub fn valid_palindrome(s: Vec<char>) -> bool {
        let mut i: usize = 0;
        let mut j: usize = s.len() - 1;

        while i < j {
            if s[i] != s[j] {
                let res1 = Self::check_palindrome(&s, i + 1, j);
                let res2 = Self::check_palindrome(&s, i, j - 1);
                return res1 || res2;
            }
            i += 1;
            j -= 1;
        }

        true
    }
}
