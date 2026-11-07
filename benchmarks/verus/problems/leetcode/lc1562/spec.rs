use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn bits_at_step(arr: Seq<i32>, n: int, step: int) -> Seq<bool>
        decreases step when step >= 0
    {
        if step <= 0 {
            Seq::new((n + 2) as nat, |i: int| false)
        } else {
            Self::bits_at_step(arr, n, step - 1).update(arr[step - 1] as int, true)
        }
    }

    pub open spec fn is_group_start(bits: Seq<bool>, n: int, m: int, l: int) -> bool {
        1 <= l && l + m - 1 <= n
        && (forall |p: int| l <= p < l + m ==> bits[p])
        && !bits[l - 1]
        && !bits[l + m]
    }

    pub open spec fn has_group_in_bits(bits: Seq<bool>, n: int, m: int) -> bool {
        exists |l: int| #[trigger] Self::is_group_start(bits, n, m, l)
    }

    pub open spec fn has_group_of_size(arr: Seq<i32>, n: int, step: int, m: int) -> bool {
        Self::has_group_in_bits(Self::bits_at_step(arr, n, step), n, m)
    }

    pub open spec fn no_group_after(arr: Seq<i32>, n: int, m: int, from: int) -> bool {
        forall |step: int| from < step && step <= n ==>
            !Self::has_group_of_size(arr, n, step, m)
    }

    pub fn find_latest_step(arr: Vec<i32>, m: i32) -> (res: i32)
        requires
            arr.len() >= 1,
            arr.len() <= 100_000,
            1 <= m <= arr.len() as i32,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= arr.len() as i32,
            forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j],
        ensures
            res == -1 || (1 <= res && res <= arr.len() as i32),
            res == -1 ==> Self::no_group_after(arr@, arr@.len() as int, m as int, 0),
            res >= 1 ==> Self::has_group_of_size(arr@, arr@.len() as int, res as int, m as int),
            res >= 1 ==> Self::no_group_after(arr@, arr@.len() as int, m as int, res as int),
    {
    }
}

}
