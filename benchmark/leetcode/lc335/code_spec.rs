use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn crossing_case1(distance: Seq<i32>, i: int) -> bool
        recommends
            0 <= i < distance.len(),
    {
        i >= 3
            && distance[i as int] as int >= distance[(i - 2) as int] as int
            && distance[(i - 1) as int] as int <= distance[(i - 3) as int] as int
    }

    pub open spec fn crossing_case2(distance: Seq<i32>, i: int) -> bool
        recommends
            0 <= i < distance.len(),
    {
        i >= 4
            && distance[(i - 1) as int] as int == distance[(i - 3) as int] as int
            && distance[i as int] as int + distance[(i - 4) as int] as int
                >= distance[(i - 2) as int] as int
    }

    pub open spec fn crossing_case3(distance: Seq<i32>, i: int) -> bool
        recommends
            0 <= i < distance.len(),
    {
        i >= 5
            && distance[(i - 2) as int] as int >= distance[(i - 4) as int] as int
            && distance[(i - 1) as int] as int <= distance[(i - 3) as int] as int
            && distance[(i - 1) as int] as int + distance[(i - 5) as int] as int
                >= distance[(i - 3) as int] as int
            && distance[i as int] as int + distance[(i - 4) as int] as int
                >= distance[(i - 2) as int] as int
    }

    pub open spec fn crossing_at(distance: Seq<i32>, i: int) -> bool
        recommends
            0 <= i < distance.len(),
    {
        Self::crossing_case1(distance, i)
            || Self::crossing_case2(distance, i)
            || Self::crossing_case3(distance, i)
    }

    pub open spec fn spec_is_self_crossing(distance: Seq<i32>) -> bool {
        exists|i: int| 0 <= i < distance.len() && Self::crossing_at(distance, i)
    }

    pub fn is_self_crossing(distance: Vec<i32>) -> (result: bool)
        requires
            1 <= distance.len() <= 100000,
            forall|i: int| 0 <= i < distance.len() ==> 1 <= #[trigger] distance[i] <= 100000,
        ensures
            result == Self::spec_is_self_crossing(distance@),
    {
        let n = distance.len();
        if n < 4 {
            return false;
        }
        let mut i: usize = 3;

        while i < n {
            let di = distance[i] as i64;
            let d_im1 = distance[i - 1] as i64;
            let d_im2 = distance[i - 2] as i64;
            let d_im3 = distance[i - 3] as i64;

            if di >= d_im2 && d_im1 <= d_im3 {
                return true;
            }

            if i >= 4 {
                let d_im4 = distance[i - 4] as i64;
                if d_im1 == d_im3 && di + d_im4 >= d_im2 {
                    return true;
                }
            }

            if i >= 5 {
                let d_im4 = distance[i - 4] as i64;
                let d_im5 = distance[i - 5] as i64;
                if d_im2 >= d_im4
                    && d_im1 <= d_im3
                    && d_im1 + d_im5 >= d_im3
                    && di + d_im4 >= d_im2
                {
                    return true;
                }
            }

            i += 1;
        }

        false
    }
}

}
