use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn diag2(d: Vec<i32>) -> int
        recommends
            d.len() == 2,
    {
        d[0] as int * d[0] as int + d[1] as int * d[1] as int
    }

    pub open spec fn area(d: Vec<i32>) -> int
        recommends
            d.len() == 2,
    {
        d[0] as int * d[1] as int
    }

    pub open spec fn best_diag_prefix(ds: Seq<Vec<i32>>, len: int) -> int
        recommends
            0 <= len <= ds.len(),
            forall |k: int| 0 <= k < ds.len() ==> ds[k].len() == 2,
        decreases len,
    {
        if len <= 0 {
            0
        } else {
            let prev = Self::best_diag_prefix(ds, len - 1);
            let cur = Self::diag2(ds[len - 1]);
            if cur > prev { cur } else { prev }
        }
    }

    pub open spec fn best_area_prefix(ds: Seq<Vec<i32>>, len: int) -> int
        recommends
            0 <= len <= ds.len(),
            forall |k: int| 0 <= k < ds.len() ==> ds[k].len() == 2,
        decreases len,
    {
        if len <= 0 {
            0
        } else {
            let prev_diag = Self::best_diag_prefix(ds, len - 1);
            let prev_area = Self::best_area_prefix(ds, len - 1);
            let cur_diag = Self::diag2(ds[len - 1]);
            let cur_area = Self::area(ds[len - 1]);
            if cur_diag > prev_diag {
                cur_area
            } else if cur_diag < prev_diag {
                prev_area
            } else if cur_area > prev_area {
                cur_area
            } else {
                prev_area
            }
        }
    }

    pub fn area_of_max_diagonal(dimensions: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= dimensions.len() <= 100,
            forall |i: int| 0 <= i < dimensions.len() ==> dimensions[i].len() == 2,
            forall |i: int| 0 <= i < dimensions.len() ==> 1 <= #[trigger] dimensions[i][0] <= 100,
            forall |i: int| 0 <= i < dimensions.len() ==> 1 <= #[trigger] dimensions[i][1] <= 100,
        ensures
            result as int == Self::best_area_prefix(dimensions@, dimensions.len() as int),
    {
        let mut best_diag: i32 = 0;
        let mut best_area: i32 = 0;
        let mut i: usize = 0;

        while i < dimensions.len() {
            let l: i32 = dimensions[i][0];
            let w: i32 = dimensions[i][1];
            let cur_diag: i32 = l * l + w * w;
            let cur_area: i32 = l * w;

            if cur_diag > best_diag || (cur_diag == best_diag && cur_area > best_area) {
                best_diag = cur_diag;
                best_area = cur_area;
            }

            i = i + 1;
        }

        best_area
    }
}

}
