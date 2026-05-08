use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_one_bit_character_spec(bits: Seq<i32>, i: int) -> bool
        decreases bits.len() - i
    {
        if i == bits.len() - 1 {
            true
        } else if i >= bits.len() {
            false
        } else {
            if bits[i] == 0 {
                Self::is_one_bit_character_spec(bits, i + 1)
            } else { 
                Self::is_one_bit_character_spec(bits, i + 2)
            }
        }
    }

    pub fn is_one_bit_character(bits: Vec<i32>) -> (res: bool) 
        requires 
            1 <= bits.len() <= 1000, 
            forall |i: int| 0 <= i < bits.len() ==> bits[i] == 0 || bits[i] == 1, 
        ensures 
            res == Self::is_one_bit_character_spec(bits@, 0), 
    {
        let n = bits.len();

        let mut i = 0;
        while (i < n - 1) 
            invariant
                1 <= bits.len() <= 1000, 
                forall |i: int| 0 <= i < bits.len() ==> bits[i] == 0 || bits[i] == 1, 
                0 <= i <= n,
                n == bits.len(),
                Self::is_one_bit_character_spec(bits@, 0) == 
                    Self::is_one_bit_character_spec(bits@, i as int),
            decreases n - i, 
        {
            i += 1 + (bits[i] as usize);
        }

        i == n - 1
    }
}

}