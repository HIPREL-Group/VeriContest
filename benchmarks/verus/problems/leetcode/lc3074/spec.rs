use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_prefix(s: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else if n > s.len() {
            Self::sum_prefix(s, s.len() as int)
        } else {
            Self::sum_prefix(s, n - 1) + s[n - 1] as int
        }
    }

    pub open spec fn max_index_prefix(s: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 1 {
            0
        } else if n > s.len() {
            Self::max_index_prefix(s, s.len() as int)
        } else {
            let j = Self::max_index_prefix(s, n - 1);
            if s[n - 1] >= s[j] {
                n - 1
            } else {
                j
            }
        }
    }

    pub open spec fn max_value(s: Seq<i32>) -> int {
        if s.len() == 0 {
            0
        } else {
            s[Self::max_index_prefix(s, s.len() as int)] as int
        }
    }

    pub open spec fn pick_max_once(s: Seq<i32>) -> Seq<i32> {
        if s.len() == 0 {
            s
        } else {
            s.update(Self::max_index_prefix(s, s.len() as int), 0)
        }
    }

    pub open spec fn after_k(s: Seq<i32>, k: int) -> Seq<i32>
        decreases k,
    {
        if k <= 0 {
            s
        } else if k > s.len() {
            Self::after_k(s, s.len() as int)
        } else {
            Self::pick_max_once(Self::after_k(s, k - 1))
        }
    }

    pub open spec fn picked_sum_k(s: Seq<i32>, k: int) -> int
        decreases k,
    {
        if k <= 0 {
            0
        } else if k > s.len() {
            Self::picked_sum_k(s, s.len() as int)
        } else {
            Self::picked_sum_k(s, k - 1) + Self::max_value(Self::after_k(s, k - 1))
        }
    }

    pub open spec fn min_boxes_from(capacity: Seq<i32>, total: int, k: int) -> int
        decreases capacity.len() - k,
    {
        if k >= capacity.len() || Self::picked_sum_k(capacity, k) >= total {
            k
        } else {
            Self::min_boxes_from(capacity, total, k + 1)
        }
    }

    pub open spec fn minimum_boxes_spec(apple: Seq<i32>, capacity: Seq<i32>) -> int {
        let total = Self::sum_prefix(apple, apple.len() as int);
        Self::min_boxes_from(capacity, total, 0)
    }

    pub fn minimum_boxes(apple: Vec<i32>, capacity: Vec<i32>) -> (result: i32)
        requires
            1 <= apple.len() <= 50,
            1 <= capacity.len() <= 50,
            forall |i: int| 0 <= i < apple.len() ==> 1 <= #[trigger] apple[i] <= 50,
            forall |i: int| 0 <= i < capacity.len() ==> 1 <= #[trigger] capacity[i] <= 50,
            Self::sum_prefix(apple@, apple.len() as int) <= Self::sum_prefix(capacity@, capacity.len() as int),
        ensures
            result as int == Self::minimum_boxes_spec(apple@, capacity@),
    {
    }
}

}
