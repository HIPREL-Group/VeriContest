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
        
    }
}

}