use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_box_upto(boxes_j: Seq<i32>, pkg: i32, end: int) -> int
        decreases end
    {
        if end <= 0 {
            -1
        } else {
            let prev = Self::min_box_upto(boxes_j, pkg, end - 1);
            let cur = boxes_j[end - 1] as int;
            if cur >= pkg as int {
                if prev == -1 || cur <= prev { cur } else { prev }
            } else {
                prev
            }
        }
    }

    pub open spec fn can_fit_upto(packages: Seq<i32>, boxes_j: Seq<i32>, end: int) -> bool
        decreases end
    {
        if end <= 0 {
            true
        } else {
            Self::can_fit_upto(packages, boxes_j, end - 1)
                && Self::min_box_upto(boxes_j, packages[end - 1], boxes_j.len() as int) >= packages[end - 1] as int
        }
    }

    pub open spec fn waste_upto(packages: Seq<i32>, boxes_j: Seq<i32>, end: int) -> int
        decreases end
    {
        if end <= 0 {
            0
        } else {
            (Self::min_box_upto(boxes_j, packages[end - 1], boxes_j.len() as int) - packages[end - 1] as int)
                + Self::waste_upto(packages, boxes_j, end - 1)
        }
    }

    pub open spec fn best_waste_upto(packages: Seq<i32>, boxes: Seq<Vec<i32>>, end: int) -> int
        decreases end
    {
        if end <= 0 {
            -1
        } else {
            let prev = Self::best_waste_upto(packages, boxes, end - 1);
            let boxes_j = boxes[end - 1]@;
            let n = packages.len() as int;
            if Self::can_fit_upto(packages, boxes_j, n) {
                let w = Self::waste_upto(packages, boxes_j, n);
                if prev == -1 || w < prev { w } else { prev }
            } else {
                prev
            }
        }
    }

    pub fn min_wasted_space(packages: Vec<i32>, boxes: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= packages.len() <= 100_000,
            forall |i: int| 0 <= i < packages.len() ==> 1 <= #[trigger] packages[i] <= 100_000,
            1 <= boxes.len() <= 100_000,
            forall |j: int| #![trigger boxes@[j]] 0 <= j < boxes@.len() ==> 1 <= boxes@[j]@.len() <= 100_000,
            forall |j: int, k: int| 0 <= j < boxes@.len() && 0 <= k < boxes@[j]@.len()
                ==> 1 <= #[trigger] boxes@[j]@[k] <= 100_000,
        ensures
            Self::best_waste_upto(packages@, boxes@, boxes@.len() as int) == -1 ==> res == -1i32,
            Self::best_waste_upto(packages@, boxes@, boxes@.len() as int) >= 0 ==>
                res == (Self::best_waste_upto(packages@, boxes@, boxes@.len() as int) % 1_000_000_007) as i32,
    {
    }
}

}
