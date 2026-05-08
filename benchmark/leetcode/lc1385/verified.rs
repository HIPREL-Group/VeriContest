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
        while i < arr1.len()
            invariant
                0 <= i <= arr1.len(),
                1 <= arr1.len() <= 500,
                1 <= arr2.len() <= 500,
                0 <= d <= 100,
                forall|k: int| 0 <= k < arr1.len() ==> -1000 <= #[trigger] arr1[k] <= 1000,
                forall|k: int| 0 <= k < arr2.len() ==> -1000 <= #[trigger] arr2[k] <= 1000,
                0 <= result <= i as i32,
                result as int == Self::distance_value_prefix(arr1@, arr2@, d, i as int),
            decreases arr1.len() - i,
        {
            let x = arr1[i];
            let mut ok: bool = true;
            let mut j: usize = 0;
            while j < arr2.len()
                invariant
                    0 <= j <= arr2.len(),
                    ok ==> forall|k: int| 0 <= k < j ==> Self::abs_int(x as int - #[trigger] arr2[k] as int) > d as int,
                    !ok ==> exists|k: int| 0 <= k < j && Self::abs_int(x as int - arr2[k] as int) <= d as int,
                decreases arr2.len() - j,
            {
                let diff = x as i64 - arr2[j] as i64;
                let abs_diff = if diff < 0 { -diff } else { diff };
                if abs_diff <= d as i64 {
                    assert(Self::abs_int(x as int - arr2@[j as int] as int) <= d as int);
                    ok = false;
                } else {
                    assert(Self::abs_int(x as int - arr2@[j as int] as int) > d as int);
                }
                j = j + 1;
            }
            if ok {
                assert(j == arr2.len());
                assert(Self::far_from_all(arr2@, x, d));
                result = result + 1;
                assert(result as int == Self::distance_value_prefix(arr1@, arr2@, d, i as int) + 1);
                assert(result as int == Self::distance_value_prefix(arr1@, arr2@, d, (i + 1) as int));
            } else {
                assert(exists|k: int| 0 <= k < arr2.len() && Self::abs_int(x as int - arr2[k] as int) <= d as int);
                assert(!Self::far_from_all(arr2@, x, d));
                assert(result as int == Self::distance_value_prefix(arr1@, arr2@, d, i as int));
                assert(result as int == Self::distance_value_prefix(arr1@, arr2@, d, (i + 1) as int));
            }
            i = i + 1;
        }
        result
    }
}

}
