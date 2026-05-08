use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    

    pub open spec fn spec_min(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn min_in_range(s: Seq<i32>, i: int, j: int) -> int
        decreases j - i,
    {
        if i >= j {
            s[i] as int
        } else {
            Self::spec_min(s[i] as int, Self::min_in_range(s, i + 1, j))
        }
    }

    pub open spec fn score_spec(s: Seq<i32>, i: int, j: int) -> int {
        Self::min_in_range(s, i, j) * (j - i + 1)
    }

    

    
    proof fn lemma_min_le_elem(s: Seq<i32>, i: int, j: int, p: int)
        requires
            0 <= i <= j < s.len(),
            i <= p <= j,
        ensures
            Self::min_in_range(s, i, j) <= s[p] as int,
        decreases j - i,
    {
        if i < j && p > i {
            Self::lemma_min_le_elem(s, i + 1, j, p);
        }
    }

    
    proof fn lemma_min_bounds(s: Seq<i32>, i: int, j: int, lo: int, hi: int)
        requires
            0 <= i <= j < s.len(),
            forall|p: int| i <= p <= j ==> lo <= #[trigger] (s[p] as int) <= hi,
        ensures
            lo <= Self::min_in_range(s, i, j) <= hi,
        decreases j - i,
    {
        if i < j {
            Self::lemma_min_bounds(s, i + 1, j, lo, hi);
        }
    }

    
    proof fn lemma_min_shrink_left(s: Seq<i32>, i: int, j: int)
        requires
            0 <= i,
            i < j,
            j < s.len(),
        ensures
            Self::min_in_range(s, i, j) <= Self::min_in_range(s, i + 1, j),
    {
        
        
    }

    
    proof fn lemma_min_extend_right(s: Seq<i32>, i: int, j: int)
        requires
            0 <= i <= j,
            j + 1 < s.len(),
        ensures
            Self::min_in_range(s, i, j + 1) == Self::spec_min(
                Self::min_in_range(s, i, j),
                s[j + 1] as int,
            ),
        decreases j - i,
    {
        if i == j {
            
            assert(Self::min_in_range(s, i + 1, j + 1) == s[j + 1] as int);
        } else {
            Self::lemma_min_extend_right(s, i + 1, j);
            
            let a = s[i] as int;
            let b = Self::min_in_range(s, i + 1, j);
            let c = s[j + 1] as int;
            
            if a <= b {
                if a <= c {
                    assert(Self::spec_min(a, Self::spec_min(b, c)) == a);
                    assert(Self::spec_min(Self::spec_min(a, b), c) == a);
                } else {
                    assert(Self::spec_min(b, c) == c);
                    assert(Self::spec_min(a, c) == c);
                    assert(Self::spec_min(Self::spec_min(a, b), c) == c);
                    assert(Self::spec_min(a, Self::spec_min(b, c)) == c);
                }
            } else {
                if b <= c {
                    assert(Self::spec_min(a, b) == b);
                    assert(Self::spec_min(b, c) == b);
                    assert(Self::spec_min(a, Self::spec_min(b, c)) == b);
                    assert(Self::spec_min(Self::spec_min(a, b), c) == b);
                } else {
                    assert(Self::spec_min(b, c) == c);
                    assert(Self::spec_min(a, c) == c);
                    assert(Self::spec_min(a, Self::spec_min(b, c)) == c);
                    assert(Self::spec_min(Self::spec_min(a, b), c) == c);
                }
            }
        }
    }

    
    proof fn lemma_min_shrink_right(s: Seq<i32>, i: int, j: int)
        requires
            0 <= i,
            i < j,
            j < s.len(),
        ensures
            Self::min_in_range(s, i, j) <= Self::min_in_range(s, i, j - 1),
    {
        Self::lemma_min_extend_right(s, i, j - 1);
        
        
    }

    

    pub fn maximum_score(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 20_000,
            0 <= k < nums.len() as i32,
        ensures
            exists|i: int, j: int|
                0 <= i && i <= k as int && k as int <= j && j < nums@.len() && result as int
                    == Self::score_spec(nums@, i, j),
            forall|i: int, j: int|
                0 <= i && i <= k as int && k as int <= j && j < nums@.len() ==> Self::score_spec(
                    nums@,
                    i,
                    j,
                ) <= result as int,
            result >= 1i32,
    {
        let n = nums.len();
        let ghost n_int = n as int;
        let k_usize = k as usize;
        let ghost k_int = k as int;
        let mut left: usize = k_usize;
        let mut right: usize = k_usize;
        let mut cur_min: i32 = nums[k_usize];
        let mut result: i32 = cur_min;

        let ghost mut wit_l: int = k_int;
        let ghost mut wit_r: int = k_int;

        
        proof {
            assert(Self::min_in_range(nums@, k_int, k_int) == nums@[k_int] as int);
            
            assert(k_int - k_int + 1 == 1int);
            assert(nums@[k_int] as int * 1 == nums@[k_int] as int);

            
            assert forall|a: int, b: int|
                0 <= a && a <= k_int && k_int <= b && b < n_int && b - a == 0int
            implies
                Self::min_in_range(nums@, a, b) <= cur_min as int
            by {
                assert(a == k_int && b == k_int);
            };

            
            assert forall|a: int, b: int|
                0 <= a && a <= k_int && k_int <= b && b < n_int && b - a + 1 <= 1int
            implies
                Self::score_spec(nums@, a, b) <= result as int
            by {
                assert(a == k_int && b == k_int);
                assert(Self::min_in_range(nums@, a, b) == nums@[k_int] as int);
            };
        }

        while left > 0 || right < n - 1
            invariant
                n == nums.len(),
                n_int == n as int,
                k_int == k as int,
                k_usize == k as usize,
                1 <= n <= 100_000,
                0 <= k_usize < n,
                forall|i: int| 0 <= i < n_int ==> 1 <= #[trigger] nums[i] <= 20_000,
                
                0 <= left <= k_usize <= right < n,
                
                cur_min as int == Self::min_in_range(nums@, left as int, right as int),
                1 <= cur_min <= 20_000,
                
                result >= 1i32,
                result as int <= 2_000_000_000,
                
                0 <= wit_l && wit_l <= k_int && k_int <= wit_r && wit_r < n_int
                    && result as int == Self::score_spec(nums@, wit_l, wit_r),
                
                forall|a: int, b: int|
                    0 <= a && a <= k_int && k_int <= b && b < n_int && b - a == right as int
                        - left as int ==> Self::min_in_range(nums@, a, b) <= cur_min as int,
                
                forall|a: int, b: int|
                    0 <= a && a <= k_int && k_int <= b && b < n_int && b - a + 1 <= right as int
                        - left as int + 1 ==> Self::score_spec(nums@, a, b)
                        <= result as int,
            decreases left + (n - 1 - right),
        {
            let ghost old_left = left as int;
            let ghost old_right = right as int;
            let ghost old_cur_min = cur_min;
            let ghost old_result = result;
            let ghost old_width = right as int - left as int;

            let left_val: i32 = if left > 0 { nums[left - 1] } else { 0 };
            let right_val: i32 = if right < n - 1 { nums[right + 1] } else { 0 };

            if left_val >= right_val {
                
                left = left - 1;
                if nums[left] < cur_min {
                    cur_min = nums[left];
                }

                proof {
                    assert(Self::min_in_range(nums@, old_left, old_right) == old_cur_min as int);

                    
                    assert forall|a: int, b: int|
                        0 <= a && a <= k_int && k_int <= b && b < n_int && b - a == right as int
                            - left as int
                    implies
                        Self::min_in_range(nums@, a, b) <= cur_min as int
                    by {
                        
                        if a < k_int {
                            assert(b - (a + 1) == old_width);
                            
                            Self::lemma_min_shrink_left(nums@, a, b);
                            
                        } else {
                            
                            assert((b - 1) - a == old_width);
                            
                            Self::lemma_min_shrink_right(nums@, a, b);
                            
                        }

                        
                        if a >= old_left {
                            assert(b >= old_right + 1);
                            Self::lemma_min_le_elem(nums@, a, b, old_right + 1);
                            
                        } else {
                            Self::lemma_min_le_elem(nums@, a, b, left as int);
                        }

                        
                        
                        
                    };
                }
            } else {
                
                right = right + 1;
                if nums[right] < cur_min {
                    cur_min = nums[right];
                }

                proof {
                    assert(Self::min_in_range(nums@, old_left, old_right) == old_cur_min as int);
                    Self::lemma_min_extend_right(nums@, left as int, old_right);
                    

                    
                    assert forall|a: int, b: int|
                        0 <= a && a <= k_int && k_int <= b && b < n_int && b - a == right as int
                            - left as int
                    implies
                        Self::min_in_range(nums@, a, b) <= cur_min as int
                    by {
                        
                        if a < k_int {
                            assert(b - (a + 1) == old_width);
                            Self::lemma_min_shrink_left(nums@, a, b);
                        } else {
                            assert((b - 1) - a == old_width);
                            Self::lemma_min_shrink_right(nums@, a, b);
                        }

                        
                        if b > old_right {
                            Self::lemma_min_le_elem(nums@, a, b, right as int);
                        } else {
                            assert(a < old_left);
                            Self::lemma_min_le_elem(nums@, a, b, old_left - 1);
                            
                        }

                        
                        
                    };
                }
            }

            
            proof {
                Self::lemma_min_bounds(nums@, left as int, right as int, 1, 20_000);
                assert(cur_min as int * (right as int - left as int + 1) <= 2_000_000_000)
                    by (nonlinear_arith)
                    requires
                        1 <= cur_min <= 20_000,
                        1 <= right as int - left as int + 1 <= 100_000,
                ;
            }

            let score: i32 = cur_min * ((right - left + 1) as i32);

            if score > result {
                result = score;
                proof {
                    wit_l = left as int;
                    wit_r = right as int;
                }
            }

            
            proof {
                assert(result as int >= cur_min as int * (right as int - left as int + 1));

                assert forall|a: int, b: int|
                    0 <= a && a <= k_int && k_int <= b && b < n_int && b - a + 1 <= right as int
                        - left as int + 1
                implies
                    Self::score_spec(nums@, a, b) <= result as int
                by {
                    if b - a + 1 < right as int - left as int + 1 {
                        assert(b - a + 1 <= old_width + 1);
                    } else {
                        
                        assert(b - a == right as int - left as int);
                        
                        assert(Self::min_in_range(nums@, a, b) <= cur_min as int);
                        Self::lemma_min_bounds(nums@, a, b, 1, 20_000);
                        
                        let ghost m = Self::min_in_range(nums@, a, b);
                        let ghost w = b - a + 1;
                        assert(m * w <= cur_min as int * w) by (nonlinear_arith)
                            requires
                                m <= cur_min as int,
                                w >= 1,
                                m >= 1,
                        ;
                        assert(w == right as int - left as int + 1);
                    }
                };
            }
        }

        result
    }
}

} 
