use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn negabinary_val(s: Seq<i32>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0int
    } else {
        s.last() as int + (-2int) * negabinary_val(s.drop_last())
    }
}

impl Solution {
    pub fn add_negabinary(arr1: Vec<i32>, arr2: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= arr1.len() <= 1000,
            1 <= arr2.len() <= 1000,
            forall|i: int| 0 <= i < arr1.len() ==> (#[trigger] arr1[i] == 0 || arr1[i] == 1),
            forall|i: int| 0 <= i < arr2.len() ==> (#[trigger] arr2[i] == 0 || arr2[i] == 1),
            arr1.len() == 1 || arr1[0] == 1,
            arr2.len() == 1 || arr2[0] == 1,
        ensures
            result.len() >= 1,
            forall|i: int|
                0 <= i < result.len() ==> (#[trigger] result[i] == 0 || result[i] == 1),
            result.len() == 1 || result[0] == 1,
            negabinary_val(result@) == negabinary_val(arr1@) + negabinary_val(arr2@),
    {
        let n1 = arr1.len();
        let n2 = arr2.len();
        let max_len = if n1 >= n2 { n1 } else { n2 };
        let max_iters = max_len + 3;
        let mut res: Vec<i32> = Vec::new();
        let mut carry: i32 = 0;
        let mut k: usize = 0;
        while k < max_iters && (k < n1 || k < n2 || carry != 0) {
            let a = if k < n1 { arr1[n1 - 1 - k] } else { 0 };
            let b = if k < n2 { arr2[n2 - 1 - k] } else { 0 };
            let sum = carry + a + b;
            let bit: i32;
            let new_carry: i32;
            if sum >= 2 {
                bit = sum - 2;
                new_carry = -1;
            } else if sum < 0 {
                bit = sum + 2;
                new_carry = 1;
            } else {
                bit = sum;
                new_carry = 0;
            }
            res.push(bit);
            carry = new_carry;
            k = k + 1;
        }
        let mut end = res.len();
        while end > 1 && res[end - 1] == 0 {
            end = end - 1;
        }
        let mut result: Vec<i32> = Vec::new();
        let mut i = end;
        while i > 0 {
            i = i - 1;
            result.push(res[i]);
        }
        result
    }
}

}
