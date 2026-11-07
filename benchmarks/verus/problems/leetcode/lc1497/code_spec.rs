use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn remainder_count(arr: Seq<i32>, k: int, r: int) -> int
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else if arr.last() as int % k == r {
        1 + remainder_count(arr.drop_last(), k, r)
    } else {
        remainder_count(arr.drop_last(), k, r)
    }
}

impl Solution {
    pub fn can_arrange(arr: Vec<i32>, k: i32) -> (result: bool)
        requires
            arr@.len() % 2 == 0,
            2 <= arr@.len() <= 100000,
            1 <= k <= 100000,
            forall|i: int| 0 <= i < arr@.len() ==> -1000000000 <= #[trigger] arr@[i] <= 1000000000,
        ensures
            result == (remainder_count(arr@, k as int, 0) % 2 == 0 && forall|r: int|
                1 <= r < k as int ==> #[trigger] remainder_count(arr@, k as int, r)
                    == remainder_count(arr@, k as int, k as int - r)),
    {
        let n = arr.len();
        let ku = k as usize;
        let mut count: Vec<i32> = Vec::new();
        let mut init = 0usize;
        while init < ku {
            count.push(0i32);
            init += 1;
        }
        let mut i = 0usize;
        while i < n {
            let elem = arr[i];
            let rem: i32;
            if elem >= 0 {
                rem = elem % k;
            } else {
                let neg_elem = -elem;
                let r = neg_elem % k;
                rem = if r == 0 { 0 } else { k - r };
            }
            let rem_u = rem as usize;
            count.set(rem_u, count[rem_u] + 1);
            i += 1;
        }
        if count[0] % 2 != 0 {
            return false;
        }
        let mut j = 1usize;
        while j < ku {
            if count[j] != count[ku - j] {
                return false;
            }
            j += 1;
        }
        true
    }
}

}
