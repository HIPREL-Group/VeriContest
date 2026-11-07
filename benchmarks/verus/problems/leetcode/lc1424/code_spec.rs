use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_diag_val(nums: Seq<Vec<i32>>, i: int) -> int
        decreases nums.len() - i
    {
        if i >= nums.len() {
            0int
        } else {
            let d = i + nums[i].len() - 1;
            let rest = Self::max_diag_val(nums, i + 1);
            if d > rest { d } else { rest }
        }
    }

    pub open spec fn diag_seg(nums: Seq<Vec<i32>>, d: int, hi: int, lo: int) -> Seq<i32>
        decreases (if hi >= lo && hi >= 0 { hi - lo + 1 } else { 0 }) as nat
    {
        if hi < lo || hi < 0 {
            Seq::<i32>::empty()
        } else {
            let j = d - hi;
            let head = if hi < nums.len() && 0 <= j && j < nums[hi].len() {
                seq![nums[hi][j]]
            } else {
                Seq::<i32>::empty()
            };
            head + Self::diag_seg(nums, d, hi - 1, lo)
        }
    }

    pub open spec fn total_len(nums: Seq<Vec<i32>>, i: int) -> int
        decreases i
    {
        if i <= 0 { 0int } else { Self::total_len(nums, i - 1) + nums[i - 1].len() as int }
    }

    pub open spec fn diag_order(nums: Seq<Vec<i32>>, max_d: int) -> Seq<i32>
        decreases (if max_d >= 0 { max_d + 1 } else { 0 }) as nat
    {
        if max_d < 0 {
            Seq::<i32>::empty()
        } else {
            let m = nums.len() as int;
            let start_i = if max_d < m { max_d } else { m - 1 };
            Self::diag_order(nums, max_d - 1) + Self::diag_seg(nums, max_d, start_i, 0)
        }
    }

    pub fn find_diagonal_order(nums: Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            1 <= nums@.len() <= 100000,
            forall |i: int| 0 <= i < nums@.len() ==>
                1 <= (#[trigger] nums@[i]).len() <= 100000,
            forall |i: int, j: int| 0 <= i < nums@.len() && 0 <= j < nums@[i].len() ==>
                1 <= (#[trigger] nums@[i][j]) <= 100000,
            1 <= Self::total_len(nums@, nums@.len() as int) <= 100000,
        ensures
            result@ == Self::diag_order(nums@, Self::max_diag_val(nums@, 0)),
    {
        let m = nums.len();

        let mut max_d: usize = 0;
        let mut i: usize = m;
        while i > 0 {
            i = i - 1;
            let d = i + nums[i].len() - 1;
            if d > max_d {
                max_d = d;
            }
        }

        let mut count: Vec<usize> = Vec::new();
        let mut k: usize = 0;
        while k <= max_d {
            count.push(0);
            k = k + 1;
        }

        let mut i2: usize = 0;
        while i2 < m {
            let row_len = nums[i2].len();
            let mut j: usize = 0;
            while j < row_len {
                let d = i2 + j;
                count[d] = count[d] + 1;
                j = j + 1;
            }
            i2 = i2 + 1;
        }

        let mut offset: Vec<usize> = Vec::new();
        offset.push(0);
        let mut k2: usize = 0;
        while k2 <= max_d {
            let next = offset[k2] + count[k2];
            offset.push(next);
            k2 = k2 + 1;
        }

        let total = offset[max_d + 1];

        let mut result: Vec<i32> = Vec::new();
        let mut z: usize = 0;
        while z < total {
            result.push(0);
            z = z + 1;
        }

        let mut cursor: Vec<usize> = Vec::new();
        let mut k3: usize = 0;
        while k3 <= max_d {
            cursor.push(offset[k3 + 1]);
            k3 = k3 + 1;
        }

        let mut i3: usize = 0;
        while i3 < m {
            let row_len3 = nums[i3].len();
            let mut j3: usize = 0;
            while j3 < row_len3 {
                let d = i3 + j3;
                let old_cursor_d = cursor[d];
                cursor[d] = cursor[d] - 1;
                let val = nums[i3][j3];
                result.set(cursor[d], val);
                j3 = j3 + 1;
            }
            i3 = i3 + 1;
        }

        result
    }
}

}
