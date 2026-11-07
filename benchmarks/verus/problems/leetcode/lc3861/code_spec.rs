use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_minimum_capacity_index(capacity: Seq<i32>, item_size: i32, idx: int) -> bool {
        0 <= idx < capacity.len()
            && capacity[idx] >= item_size
            && forall |j: int| 0 <= j < capacity.len() && capacity[j] >= item_size ==> capacity[idx] <= #[trigger] capacity[j]
            && forall |j: int| 0 <= j < capacity.len() && capacity[j] >= item_size && capacity[j] == capacity[idx] ==> idx <= j
    }

    pub open spec fn valid_result(capacity: Seq<i32>, item_size: i32, res: int) -> bool {
        (res == -1 && forall |j: int| 0 <= j < capacity.len() ==> #[trigger] capacity[j] < item_size)
            || (0 <= res && Self::is_minimum_capacity_index(capacity, item_size, res))
    }

    pub fn minimum_index(capacity: Vec<i32>, item_size: i32) -> (res: i32)
        requires
            1 <= capacity.len() <= 100,
            forall |k: int| 0 <= k < capacity.len() ==> 1 <= #[trigger] capacity[k] <= 100,
            1 <= item_size <= 100,
        ensures
            Self::valid_result(capacity@, item_size, res as int),
    {
        let n = capacity.len();
        let mut i: usize = 0;
        let mut found: bool = false;
        let mut best_idx: usize = 0;
        let mut best_cap: i32 = 0;

        while i < n {
            let cap_i = capacity[i];
            if cap_i >= item_size {
                if !found {
                    found = true;
                    best_idx = i;
                    best_cap = cap_i;
                } else if cap_i < best_cap {
                    found = true;
                    best_idx = i;
                    best_cap = cap_i;
                }
            }
            i = i + 1;
        }

        if found {
            best_idx as i32
        } else {
            -1
        }
    }
}

}
