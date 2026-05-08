use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_in_arr(arr: Seq<i32>, val: int) -> bool {
        exists |i: int| 0 <= i < arr.len() && arr[i] as int == val
    }

    pub open spec fn count_missing_up_to(arr: Seq<i32>, val: int) -> int
        decreases val
    {
        if val <= 0 { 0 }
        else {
            (if !Self::is_in_arr(arr, val) { 1int } else { 0int })
            + Self::count_missing_up_to(arr, val - 1)
        }
    }

    pub fn find_kth_positive(arr: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= arr.len() <= 1000,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1000,
            1 <= k <= 1000,
            forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] < arr[j],
        ensures
            result >= 1,
            !Self::is_in_arr(arr@, result as int),
            Self::count_missing_up_to(arr@, result as int) == k as int,
    {
        let mut missing: i32 = 0;
        let mut current: i32 = 1;
        let mut idx: usize = 0;

        while missing < k
            invariant
                0 <= idx <= arr.len(),
                1 <= current,
                0 <= missing <= k,
                1 <= arr.len() <= 1000,
                forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1000,
                1 <= k <= 1000,
                forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] < arr[j],
                current as int == 1 + idx as int + missing as int,
                missing as int == Self::count_missing_up_to(arr@, (current - 1) as int),
                forall |i: int| 0 <= i < idx as int ==> arr[i] < current,
                idx < arr.len() ==> arr[idx as int] >= current,
                current >= 2 ==> Self::count_missing_up_to(arr@, (current - 2) as int) < k as int,
            decreases arr.len() as int + k as int - idx as int - missing as int,
        {
            if idx < arr.len() && arr[idx] == current {
                proof {
                    assert(arr@[idx as int] as int == current as int);
                    assert(Self::is_in_arr(arr@, current as int));
                }
                idx = idx + 1;
                proof {
                    if (idx as int) < arr.len() {
                        assert(arr@[(idx - 1) as int] < arr@[idx as int]);
                    }
                }
            } else {
                proof {
                    assert forall |i: int| 0 <= i < arr@.len()
                        implies arr@[i] as int != current as int
                    by {
                        if i < idx as int {
                        } else if (idx as int) < arr@.len() {
                            if i > idx as int {
                                assert(arr@[idx as int] < arr@[i]);
                            }
                        }
                    };
                    assert(!Self::is_in_arr(arr@, current as int));
                }
                missing = missing + 1;
            }
            current = current + 1;
        }

        proof {
            let r = (current - 1) as int;
            assert(Self::count_missing_up_to(arr@, r) == k as int);
            assert(Self::count_missing_up_to(arr@, r - 1) < k as int);
        }

        current - 1
    }
}

}
