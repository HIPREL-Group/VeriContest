use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn xor_fold_spec(derived: Seq<i32>, idx: int, acc: i32) -> i32
        decreases derived.len() - idx,
    {
        if idx >= derived.len() {
            acc
        } else {
            Self::xor_fold_spec(derived, idx + 1, acc ^ derived[idx])
        }
    }

    pub open spec fn xor_all_spec(derived: Seq<i32>, idx: int) -> i32 {
        Self::xor_fold_spec(derived, idx, 0)
    }

    pub open spec fn does_valid_array_exist_spec(derived: Seq<i32>) -> bool {
        Self::xor_all_spec(derived, 0) == 0
    }

    fn xor_all_exec(derived: &Vec<i32>, idx: usize) -> (res: i32)
    {
        let mut i: usize = idx;
        let mut acc: i32 = 0;
        while i < derived.len() {
            acc = acc ^ derived[i];
            i = i + 1;
        }
        acc
    }

    pub fn does_valid_array_exist(derived: Vec<i32>) -> (result: bool)
        requires
            1 <= derived.len() <= 100_000,
            forall |i: int| 0 <= i < derived.len() ==> (derived[i] == 0 || derived[i] == 1),
        ensures
            result == Self::does_valid_array_exist_spec(derived@),
    {
        Self::xor_all_exec(&derived, 0) == 0
    }
}

}
