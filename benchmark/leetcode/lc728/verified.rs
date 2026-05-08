use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_dividing_number_spec(n: int) -> bool {
        n > 0 && Self::all_digits_divide_spec(n, n)
    }
    
    pub open spec fn all_digits_divide_spec(original: int, remaining: int) -> bool 
        decreases remaining, 
    {
        if remaining <= 0 {
            true
        } else {
            let digit = remaining % 10;
            digit != 0 && original % digit == 0 && 
                Self::all_digits_divide_spec(original, remaining / 10)
        }
    }

    pub fn is_dividing_number(n: i32) -> (result: bool)
        requires
            n > 0,
        ensures
            result == Self::is_dividing_number_spec(n as int),
    {
        let mut num = n;
        while num > 0 
            invariant
                n > 0,
                num >= 0,
                Self::is_dividing_number_spec(n as int) == 
                    (Self::all_digits_divide_spec(n as int, num as int)),
            decreases num, 
        {
            let digit = num % 10;
            if digit == 0 || n % digit != 0 {
                return false;
            }
            num = num / 10;
        }
        true
    }

    pub fn self_dividing_numbers(left: i32, right: i32) -> (res: Vec<i32>) 
        requires
            1 <= left <= right <= 10_000, 
        ensures 
            forall |i: int| left <= i <= right ==> 
                #[trigger] res@.contains(i as i32) == Self::is_dividing_number_spec(i), 
            forall |i: int| 0 <= i < res@.len() ==> 
                left <= #[trigger] res@[i] && res@[i] <= right,
            forall |i: int| 0 <= i < res@.len() ==> 
                Self::is_dividing_number_spec(res@[i] as int), 
            forall |i: int, j: int| 0 <= i < j < res@.len() ==> res@[i] < res@[j],
    {
        let mut result: Vec<i32> = Vec::new();
        let mut current = left;
        
        while current <= right
            invariant
                1 <= left <= right <= 10_000,
                left <= current <= right + 1,
                forall |i: int| left <= i < current ==> 
                    #[trigger] result@.contains(i as i32) == Self::is_dividing_number_spec(i),
                forall |i: int| 0 <= i < result@.len() ==> 
                    Self::is_dividing_number_spec(result@[i] as int),
                forall |i: int| 0 <= i < result@.len() ==> 
                    left <= #[trigger] result@[i as int] < current,
                forall |i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
            decreases right - current + 1, 
        {
            if Self::is_dividing_number(current) {
                let ghost old_result = result@;
                
                result.push(current);

                assert(result@.contains(current)) by {
                    assert(result@[result@.len() - 1] == current);
                }
                
                assert forall |j: int| 0 <= j < old_result.len() 
                    implies result@[j] == old_result[j] by {}
                
                assert(forall |i: int| left <= i <= current ==> 
                    #[trigger] result@.contains(i as i32) == Self::is_dividing_number_spec(i)) by {
                    assert forall |i: int| left <= i <= current
                        implies #[trigger] result@.contains(i as i32) == Self::is_dividing_number_spec(i) by {
                        if i < current {
                            assert(old_result.contains(i as i32) == Self::is_dividing_number_spec(i));
                            assert(result@.contains(i as i32) == old_result.contains(i as i32));
                        } else {
                            assert(i == current);
                            assert(result@.contains(current));
                            assert(result@.contains(i as i32));
                            assert(Self::is_dividing_number_spec(i));
                        }
                    }
                }
                assert forall |i: int, j: int| 0 <= i < j < result@.len() implies result@[i] < result@[j] by {
                    if j < old_result.len() {
                        assert(old_result[i] < old_result[j]);
                        assert(result@[i] == old_result[i]);
                        assert(result@[j] == old_result[j]);
                    } else {
                        assert(j == old_result.len());
                        assert(result@[j] == current);
                        assert(result@[i] == old_result[i]);
                        assert(old_result[i] < current);
                    }
                }
            } else {
                assert(forall |i: int| left <= i <= current ==> 
                    #[trigger] result@.contains(i as i32) == Self::is_dividing_number_spec(i)) by {
                    assert forall |i: int| left <= i <= current
                        implies #[trigger] result@.contains(i as i32) == Self::is_dividing_number_spec(i) by {
                        if i < current {
                            assert(result@.contains(i as i32) == Self::is_dividing_number_spec(i));
                        } else {
                            assert(i == current);
                            assert(!Self::is_dividing_number_spec(i));
                            assert(!result@.contains(i as i32));
                        }
                    }
                }
            } 
            current = current + 1;
        }
        
        result
    }
}

}