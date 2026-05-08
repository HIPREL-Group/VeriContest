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
        if start >= end {
            proof {
                assert forall |k: int| 0 <= k && k <= (end as int - start as int) / 2 implies #[trigger] s@[start as int + k] == s@[end as int - k] by {
                    if start as int == end as int {
                        assert(k == 0);
                        assert(s@[start as int + k] == s@[end as int - k]);
                    } else {
                        let Y = end as int - start as int;
                        assert(Y < 0);
                        assert(Y / 2 < 0) by (nonlinear_arith) requires Y < 0 {};
                        assert(false);
                    }
                };
            }
            return true;
        }
        
        let mut i = start;
        let mut j = end;
        
        while i < j
            invariant
                0 <= start <= i <= s.len(),
                0 <= j <= end < s.len(),
                start <= end,
                i as int <= j as int + 1,
                i as int + j as int == start as int + end as int,
                forall |k: int| 0 <= k < i - start ==> #[trigger] s@[start as int + k] == s@[end as int - k],
            decreases j as int - i as int + 1,
        {
            if s[i] != s[j] {
                proof {
                    let Y = end as int - start as int;
                    let X = i as int - start as int;
                    let k = X;
                    
                    assert(i < j);
                    assert(2 * X < Y);
                    assert(k <= Y / 2) by (nonlinear_arith) requires 2 * X < Y, k == X {};
                    
                    assert(start as int + k == i as int);
                    assert(end as int - k == j as int);
                    assert(s@[start as int + k] != s@[end as int - k]);
                }
                return false;
            }
            i += 1;
            j -= 1;
        }
        
        proof {
            let Y = end as int - start as int;
            assert forall |k: int| 0 <= k && k <= Y / 2 implies #[trigger] s@[start as int + k] == s@[end as int - k] by {
                let X = i as int - start as int;
                if k < X {
                    
                } else {
                    assert(i as int >= j as int);
                    assert(2 * X >= Y);
                    assert(2 * k <= Y) by (nonlinear_arith) requires k <= Y / 2 {};
                    
                    assert(k == X) by {
                        if k > X {
                            assert(k >= X + 1);
                            assert(2 * k >= 2 * X + 2) by (nonlinear_arith) requires k >= X + 1 {};
                            assert(2 * k > Y);
                            assert(false);
                        }
                    };
                    
                    assert(start as int + k == i as int);
                    assert(end as int - k == j as int);
                    
                    if i as int == j as int {
                        assert(s@[i as int] == s@[j as int]);
                    } else {
                        assert(i as int > j as int);
                        assert(2 * X > Y);
                        assert(X > Y / 2) by (nonlinear_arith) requires 2 * X > Y {};
                        assert(false);
                    }
                }
            };
        }
        
        true
    }

    
    pub fn valid_palindrome(s: Vec<char>) -> (res: bool)
        requires
            1 <= s.len() <= 100000,
        ensures
            res == Solution::valid_palindrome_spec(s@),
    {
        let mut i: usize = 0;
        let mut j: usize = s.len() - 1;

        while i < j
            invariant
                0 <= i <= s.len(),
                0 <= j < s.len(),
                i as int <= j as int + 1,
                i as int + j as int == s.len() - 1,
                Solution::valid_palindrome_rec(s@, 0, s.len() as int - 1) == Solution::valid_palindrome_rec(s@, i as int, j as int),
            decreases j as int - i as int + 1,
        {
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

} 
