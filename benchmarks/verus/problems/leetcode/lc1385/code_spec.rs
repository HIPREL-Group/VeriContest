use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_int(x: int) -> int {
        if x < 0 { -x } else { x }
    }

    pub open spec fn far_from_all(arr2: Seq<i32>, x: i32, d: i32) -> bool {
        forall|j: int| 0 <= j < arr2.len() ==> Self::abs_int(x as int - #[trigger] arr2[j] as int) > d as int
    }

    pub open spec fn distance_value_prefix(arr1: Seq<i32>, arr2: Seq<i32>, d: i32, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::distance_value_prefix(arr1, arr2, d, end - 1)
                + if Self::far_from_all(arr2, arr1[end - 1], d) { 1int } else { 0int }
        }
    }

    pub fn find_the_distance_value(arr1: Vec<i32>, arr2: Vec<i32>, d: i32) -> (result: i32)
        requires
            1 <= arr1.len() <= 500,
            1 <= arr2.len() <= 500,
            0 <= d <= 100,
            forall|i: int| 0 <= i < arr1.len() ==> -1000 <= #[trigger] arr1[i] <= 1000,
            forall|j: int| 0 <= j < arr2.len() ==> -1000 <= #[trigger] arr2[j] <= 1000,
        ensures
            0 <= result <= arr1.len() as i32,
            result as int == Self::distance_value_prefix(arr1@, arr2@, d, arr1.len() as int),
    {
        let mut result: i32 = 0;
        let mut i: usize = 0;
        while i < arr1.len() {
            let x = arr1[i];
            let mut ok: bool = true;
            let mut j: usize = 0;
            while j < arr2.len() {
                let diff = x as i64 - arr2[j] as i64;
                let abs_diff = if diff < 0 { -diff } else { diff };
                if abs_diff <= d as i64 {
                    ok = false;
                }
                j = j + 1;
            }
            if ok {
                result = result + 1;
            }
            i = i + 1;
        }
        result
    }
}

}
