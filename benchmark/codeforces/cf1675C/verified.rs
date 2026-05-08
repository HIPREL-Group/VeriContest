use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn rightmost_one(s: Seq<u8>, len: int) -> int
    decreases len,
{
    if len <= 0 {
        0int
    } else if s[len - 1] == 1u8 {
        len - 1
    } else {
        rightmost_one(s, len - 1)
    }
}

pub open spec fn leftmost_zero(s: Seq<u8>, start: int) -> int
    decreases s.len() - start,
{
    if start >= s.len() {
        s.len() - 1
    } else if s[start] == 0u8 {
        start
    } else {
        leftmost_zero(s, start + 1)
    }
}


proof fn lemma_rightmost_one_bounds(s: Seq<u8>, len: int)
    requires
        0 <= len <= s.len(),
    ensures
        0 <= rightmost_one(s, len),
        len > 0 ==> rightmost_one(s, len) < len,
    decreases len,
{
    if len <= 0 {
    } else if s[len - 1] == 1u8 {
    } else {
        lemma_rightmost_one_bounds(s, len - 1);
    }
}


proof fn lemma_leftmost_zero_bounds(s: Seq<u8>, start: int)
    requires
        0 <= start <= s.len(),
        s.len() >= 1,
    ensures
        0 <= leftmost_zero(s, start) < s.len(),
        leftmost_zero(s, start) >= start || leftmost_zero(s, start) == s.len() - 1,
    decreases s.len() - start,
{
    if start >= s.len() {
    } else if s[start] == 0u8 {
    } else {
        lemma_leftmost_zero_bounds(s, start + 1);
    }
}


proof fn lemma_rightmost_one_step(s: Seq<u8>, len: int)
    requires
        0 <= len < s.len(),
    ensures
        s[len] == 1u8 ==> rightmost_one(s, len + 1) == len,
        s[len] != 1u8 ==> rightmost_one(s, len + 1) == rightmost_one(s, len),
{
    reveal_with_fuel(rightmost_one, 2);
}








proof fn lemma_no_zero_skip(s: Seq<u8>, j: int)
    requires
        0 <= j <= s.len(),
        s.len() >= 1,
        forall|k: int| 0 <= k < j ==> s[k] != 0u8,
    ensures
        leftmost_zero(s, 0) == leftmost_zero(s, j),
    decreases j,
{
    if j <= 0 {
    } else {
        assert(s[0] != 0u8);
        lemma_no_zero_skip(s, j - 1);
        
        
        
        
        
        assert(s[j - 1] != 0u8);
        assert(j - 1 < s.len());
        
        
        reveal_with_fuel(leftmost_zero, 2);
    }
}


proof fn lemma_zero_at(s: Seq<u8>, j: int)
    requires
        0 <= j < s.len(),
        s[j] == 0u8,
    ensures
        leftmost_zero(s, j) == j,
{
    reveal_with_fuel(leftmost_zero, 2);
}


proof fn lemma_rightmost_one_continue(s: Seq<u8>, len: int)
    requires
        0 <= len < s.len(),
        s[len] != 1u8,
    ensures
        rightmost_one(s, len + 1) == rightmost_one(s, len),
{
    reveal_with_fuel(rightmost_one, 2);
}


proof fn lemma_rightmost_one_set(s: Seq<u8>, len: int)
    requires
        0 <= len < s.len(),
        s[len] == 1u8,
    ensures
        rightmost_one(s, len + 1) == len,
{
    reveal_with_fuel(rightmost_one, 2);
}

impl Solution {
    pub fn count_suspects(s: Vec<u8>) -> (result: usize)
        requires
            1 <= s.len() <= 200000,
            forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] <= 2u8,
            rightmost_one(s@, s.len() as int) <= leftmost_zero(s@, 0),
        ensures
            1 <= result <= s.len(),
            result as int == leftmost_zero(s@, 0) - rightmost_one(s@, s.len() as int) + 1,
    {
        let n = s.len();
        let mut last_one: usize = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == s.len(),
                last_one as int == rightmost_one(s@, i as int),
                0 <= last_one as int,
                i > 0 ==> (last_one as int) < (i as int),
            decreases n - i,
        {
            proof {
                lemma_rightmost_one_bounds(s@, i as int);
            }
            if s[i] == 1u8 {
                proof { lemma_rightmost_one_set(s@, i as int); }
                last_one = i;
            } else {
                proof { lemma_rightmost_one_continue(s@, i as int); }
            }
            i += 1;
            proof {
                lemma_rightmost_one_bounds(s@, i as int);
            }
        }
        let mut first_zero: usize = n - 1;
        let mut j: usize = 0;
        let mut found_zero: bool = false;
        while j < n
            invariant
                0 <= j <= n,
                n == s.len(),
                n >= 1,
                found_zero ==> (first_zero as int == leftmost_zero(s@, 0) && (first_zero as int) < (j as int) && s@[first_zero as int] == 0u8),
                !found_zero ==> (forall|k: int| 0 <= k < j ==> s@[k] != 0u8) && first_zero as int == n - 1,
            decreases n - j,
        {
            if s[j] == 0u8 && !found_zero {
                proof {
                    lemma_no_zero_skip(s@, j as int);
                    lemma_zero_at(s@, j as int);
                }
                first_zero = j;
                found_zero = true;
            }
            j += 1;
        }
        proof {
            lemma_rightmost_one_bounds(s@, n as int);
            if !found_zero {
                lemma_no_zero_skip(s@, n as int);
                
                reveal_with_fuel(leftmost_zero, 2);
            }
            assert(first_zero as int >= rightmost_one(s@, n as int));
        }
        first_zero - last_one + 1
    }
}

}
