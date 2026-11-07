use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count(s: Seq<i32>, v: i32) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            (if s[0] == v { 1int } else { 0int }) + Self::count(s.subrange(1, s.len() as int), v)
        }
    }

    pub fn find_special_integer(arr: Vec<i32>) -> (res: i32)
        requires
            1 <= arr.len() <= 10_000,
            forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 100_000,
            forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
            exists|v: i32| #[trigger] Self::count(arr@, v) > arr.len() as int / 4,
            forall|v1: i32, v2: i32| (Self::count(arr@, v1) > arr.len() as int / 4
                && Self::count(arr@, v2) > arr.len() as int / 4) ==> v1 == v2,
        ensures
            Self::count(arr@, res) > arr.len() as int / 4,
    {
        let n = arr.len();
        let quarter = n / 4;
        let mut i: usize = 0;
        while i + quarter < n {
            if arr[i] == arr[i + quarter] {
                return arr[i];
            }
            i += 1;
        }
        arr[0]
    }
}

}
