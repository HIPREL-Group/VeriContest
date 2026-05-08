use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_spec(s: Seq<i32>, start: int, end: int) -> int
        decreases end - start,
    {
        if start >= end {
            0
        } else {
            s[start] as int + Self::sum_spec(s, start + 1, end)
        }
    }

    proof fn sum_spec_append(s: Seq<i32>, start: int, end: int)
        requires
            0 <= start <= end < s.len(),
        ensures
            Self::sum_spec(s, start, end + 1) == Self::sum_spec(s, start, end) + s[end] as int,
        decreases end - start,
    {
        
        assert(Self::sum_spec(s, start, end + 1) == s[start] as int + Self::sum_spec(s, start + 1, end + 1));
        if start < end {
            assert(Self::sum_spec(s, start, end) == s[start] as int + Self::sum_spec(s, start + 1, end));
            Self::sum_spec_append(s, start + 1, end);
        }
    }

    proof fn sum_spec_nonneg(s: Seq<i32>, start: int, end: int)
        requires
            0 <= start <= end <= s.len(),
            forall|i: int| start <= i < end ==> s[i] >= 1,
        ensures
            Self::sum_spec(s, start, end) >= (end - start),
        decreases end - start,
    {
        if start < end {
            Self::sum_spec_nonneg(s, start + 1, end);
        }
    }

    pub fn candy(ratings: Vec<i32>) -> (result: i32)
        requires
            1 <= ratings.len() <= 20_000,
            forall|i: int| 0 <= i < ratings.len() ==> 0 <= #[trigger] ratings[i] <= 20_000,
        ensures
            exists|candies: Seq<i32>|
                {
                    &&& candies.len() == ratings.len()
                    &&& (forall|i: int|
                        0 <= i < candies.len() ==> #[trigger] candies[i] >= 1)
                    &&& (forall|i: int|
                        0 < i < ratings.len() && ratings[i] > ratings[i - 1] ==> #[trigger] candies[i]
                            > candies[i - 1])
                    &&& (forall|i: int|
                        0 <= i < ratings.len() - 1 && ratings[i] > ratings[i + 1] ==> #[trigger] candies[i]
                            > candies[i + 1])
                    &&& result == Self::sum_spec(candies, 0, candies.len() as int)
                },
            result >= ratings.len(),
    {
        let n = ratings.len();

        
        let mut left: Vec<i32> = Vec::new();
        left.push(1i32);
        let mut i: usize = 1;
        while i < n
            invariant
                n == ratings.len(),
                1 <= n <= 20_000,
                left.len() == i,
                1 <= i <= n,
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] left[j] <= (j + 1) as i32,
                forall|j: int|
                    0 < j < i && ratings[j] > ratings[j - 1] ==> #[trigger] left[j] == left[j - 1] + 1,
                forall|j: int|
                    0 < j < i && !(ratings[j] > ratings[j - 1]) ==> #[trigger] left[j] == 1i32,
                forall|k: int|
                    0 <= k < ratings.len() ==> 0 <= #[trigger] ratings[k] <= 20_000,
            decreases n - i,
        {
            if ratings[i] > ratings[i - 1] {
                let v = left[i - 1] + 1;
                left.push(v);
            } else {
                left.push(1i32);
            }
            i += 1;
        }
        assert(left.len() == n);

        
        let mut right: Vec<i32> = Vec::new();
        i = 0;
        while i < n
            invariant
                right.len() == i,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> #[trigger] right[j] == 1i32,
            decreases n - i,
        {
            right.push(1i32);
            i += 1;
        }
        assert(right.len() == n);

        if n >= 2 {
            let mut idx: usize = n - 1;
            while idx > 0
                invariant
                    n == ratings.len(),
                    1 <= n <= 20_000,
                    right.len() == n,
                    0 <= idx < n,
                    forall|k: int|
                        0 <= k < ratings.len() ==> 0 <= #[trigger] ratings[k] <= 20_000,
                    forall|j: int|
                        idx <= j < n - 1 && ratings[j] > ratings[j + 1] ==> #[trigger] right[j] == right[j
                            + 1] + 1,
                    forall|j: int|
                        idx <= j < n - 1 && !(ratings[j] > ratings[j + 1]) ==> #[trigger] right[j]
                            == 1i32,
                    right[n - 1] == 1i32,
                    forall|j: int|
                        idx <= j < n ==> 1 <= #[trigger] right[j] <= (n - j) as i32,
                    forall|j: int| 0 <= j < idx ==> #[trigger] right[j] == 1i32,
                decreases idx,
            {
                idx -= 1;
                if ratings[idx] > ratings[idx + 1] {
                    let v = right[idx + 1] + 1;
                    right.set(idx, v);
                }
            }
        }

        
        proof {
            if n < 2 {
                assert(forall|j: int| 0 <= j < n ==> 1 <= #[trigger] right[j] <= (n - j) as i32);
            }
        }

        
        let mut candy: Vec<i32> = Vec::new();
        i = 0;
        while i < n
            invariant
                n == ratings.len(),
                1 <= n <= 20_000,
                left.len() == n,
                right.len() == n,
                candy.len() == i,
                0 <= i <= n,
                forall|j: int| 0 <= j < n ==> 1 <= #[trigger] left[j] <= (j + 1) as i32,
                forall|j: int| 0 <= j < n ==> 1 <= #[trigger] right[j] <= (n - j) as i32,
                forall|j: int|
                    0 <= j < i ==> #[trigger] candy[j] == (if left[j] > right[j] {
                        left[j]
                    } else {
                        right[j]
                    }),
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] candy[j] <= n as i32,
            decreases n - i,
        {
            let c = if left[i] > right[i] { left[i] } else { right[i] };
            proof {
                if left[i as int] > right[i as int] {
                    assert(c == left[i as int]);
                    assert(c <= (i + 1) as i32);
                    assert(c <= n as i32);
                } else {
                    assert(c == right[i as int]);
                    assert(c <= (n - i) as i32);
                    assert(c <= n as i32);
                }
            }
            candy.push(c);
            i += 1;
        }
        assert(candy.len() == n);

        
        let mut total: i32 = 0;
        i = 0;
        while i < n
            invariant
                n == ratings.len(),
                1 <= n <= 20_000,
                candy.len() == n,
                0 <= i <= n,
                forall|j: int| 0 <= j < n ==> 1 <= #[trigger] candy[j] <= n as i32,
                total == Self::sum_spec(candy@, 0, i as int),
                0 <= total,
                total as int >= i as int,
                total as int <= (i as int) * (n as int),
            decreases n - i,
        {
            proof {
                Self::sum_spec_append(candy@, 0, i as int);
                assert(total as int + candy@[i as int] as int
                    <= (i as int) * (n as int) + (n as int))
                    by (nonlinear_arith)
                    requires
                        total as int <= (i as int) * (n as int),
                        candy@[i as int] as int <= n as int,
                ;
                assert((i as int + 1) * (n as int) == (i as int) * (n as int) + (n as int))
                    by (nonlinear_arith);
                assert(total as int + candy@[i as int] as int <= 400_000_001)
                    by (nonlinear_arith)
                    requires
                        total as int + candy@[i as int] as int
                            <= (i as int) * (n as int) + (n as int),
                        i as int >= 0,
                        i as int + 1 <= n as int,
                        n as int >= 1,
                        n as int <= 20000,
                ;
            }
            total += candy[i];
            i += 1;
        }

        
        proof {
            let witness = candy@;

            
            assert(forall|j: int| 0 <= j < witness.len() ==> #[trigger] witness[j] >= 1);

            
            assert forall|j: int|
                0 < j < ratings.len() && ratings[j] > ratings[j - 1] implies #[trigger] witness[j]
                    > witness[j - 1] by {
                
                
                
                assert(left@[j] == left@[j - 1] + 1);
                assert(!(ratings@[j - 1] > ratings@[j]));
                assert(right@[j - 1] == 1i32);
                
                
            };

            
            assert forall|j: int|
                0 <= j < ratings.len() - 1 && ratings[j] > ratings[j + 1] implies #[trigger] witness[j]
                    > witness[j + 1] by {
                
                
                
                assert(right@[j] == right@[j + 1] + 1);
                assert(!(ratings@[j + 1] > ratings@[j]));
                assert(left@[j + 1] == 1i32);
                
                
            };

            
            assert(total == Self::sum_spec(witness, 0, witness.len() as int));

            
            Self::sum_spec_nonneg(witness, 0, witness.len() as int);
        }

        total
    }
}

}
