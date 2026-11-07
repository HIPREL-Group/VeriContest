use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn same_multiset(left: Seq<i32>, right: Seq<i32>) -> bool {
    left.len() == right.len() && left.to_multiset() =~= right.to_multiset()
}

pub open spec fn sorted_adjacent_steps_at_most_one(s: Seq<i32>, n: int) -> bool {
    n <= s.len()
        && forall|i: int|
            0 <= i < n - 1 ==> {
                &&& #[trigger] s[i] <= s[i + 1]
                &&& (s[i + 1] as int - s[i] as int) <= 1
            }
}

pub open spec fn spec_remove_smallest_possible(a: Seq<i32>) -> bool {
    a.len() >= 1 && exists|s: Seq<i32>|
        s.len() == a.len() && same_multiset(s, a)
            && sorted_adjacent_steps_at_most_one(s, a.len() as int)
}

impl Solution {
    pub fn remove_smallest_possible(a: Vec<i32>) -> (res: bool)
        requires
            1 <= a.len() <= 50,
            forall|i: int| 0 <= i < a.len() as int ==> 1 <= #[trigger] a[i] as int <= 100,
        ensures
            res == spec_remove_smallest_possible(a@),
    {
        let n = a.len();
        if n == 1 {
            return true;
        }
        let mut arr = Vec::new();
        let mut i = 0usize;
        while i < n {
            arr.push(a[i]);
            i += 1;
        }
        i = 0usize;
        while i < n {
            let mut min_idx = i;
            let mut j = i + 1;
            while j < n {
                if arr[j] < arr[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }
            if i != min_idx {
                let tmp = arr[i];
                arr.set(i, arr[min_idx]);
                arr.set(min_idx, tmp);
            }
            i += 1;
        }
        let mut k = 0usize;
        while k + 1 < n {
            if (arr[k + 1] as i64) > (arr[k] as i64) + 1 {
                return false;
            }
            k += 1;
        }
        true
    }
}

}
