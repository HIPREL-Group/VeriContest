use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn appears_in_row(nums: Seq<Seq<i32>>, row: int, v: int, end: int) -> bool {
        exists|r: int| 0 <= r < end && #[trigger] nums[row][r] == v
    }

    pub open spec fn in_all_arrays(nums: Seq<Seq<i32>>, v: int, end: int) -> bool {
        forall|q: int| 0 <= q < end ==> #[trigger] Self::appears_in_row(nums, q, v, nums[q].len() as int)
    }

    pub fn intersection(nums: Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 1000,
            forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i].len() >= 1,
            forall|i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums[i].len() ==> 1 <= #[trigger] nums[i][j] <= 1000,
        ensures
            forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000,
            forall |i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
            forall|p: int| 0 <= p < result.len() ==> #[trigger] Self::in_all_arrays(nums.deep_view(), result[p] as int, nums.len() as int),
            forall|v: int| 1 <= v <= 1000 && #[trigger] Self::in_all_arrays(nums.deep_view(), v, nums.len() as int) ==>
                exists|p: int| 0 <= p < result.len() && result[p] as int == v,
    {
        let ghost nums_seq: Seq<Seq<i32>> = nums.deep_view();

        let mut out: Vec<i32> = Vec::new();
        if nums.len() == 0 {
            return out;
        }
        let mut v: i32 = 1;
        while v <= 1000
            invariant
                1 <= v <= 1001,
                nums_seq =~= nums.deep_view(),
                1 <= nums.len() <= 1000,
                forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i].len() >= 1,
                forall|i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums[i].len() ==> 1 <= #[trigger] nums[i][j] <= 1000,
                forall |i: int| 0 <= i < out.len() ==> 1 <= #[trigger] out[i] <= 1000,
                forall |i: int, j: int| 0 <= i < j < out.len() ==> out[i] < out[j],
                forall |i: int| 0 <= i < out.len() ==> out[i] < v,
                forall|p: int| 0 <= p < out.len() ==> #[trigger] Self::in_all_arrays(nums_seq, out[p] as int, nums.len() as int),
                forall|u: int| 1 <= u < v && #[trigger] Self::in_all_arrays(nums_seq, u, nums.len() as int) ==>
                    exists|p: int| 0 <= p < out.len() && out[p] as int == u,
            decreases 1001 - v,
        {
            let mut all = true;
            let mut q: usize = 0;
            let ghost mut bad_row: int = 0;
            while q < nums.len() && all
                invariant
                    0 <= q <= nums.len(),
                    1 <= v <= 1000,
                    nums_seq =~= nums.deep_view(),
                    1 <= nums.len() <= 1000,
                    forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i].len() >= 1,
                    forall|i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums[i].len() ==> 1 <= #[trigger] nums[i][j] <= 1000,
                    all ==> Self::in_all_arrays(nums_seq, v as int, q as int),
                    !all ==> (0 <= bad_row < nums.len() as int && !Self::appears_in_row(nums_seq, bad_row, v as int, nums_seq[bad_row].len() as int)),
                decreases (if all { (nums.len() - q) + 1 } else { 0 }),
            {
                let row_len = nums[q].len();
                let mut found = false;
                let mut r: usize = 0;

                proof {
                    assert(nums_seq[q as int] =~= nums@[q as int]@);
                }

                while r < row_len
                    invariant
                        q < nums.len(),
                        row_len == nums[q as int].len(),
                        0 <= r <= row_len,
                        1 <= v <= 1000,
                        nums_seq =~= nums.deep_view(),
                        nums_seq[q as int] =~= nums@[q as int]@,
                        found <==> Self::appears_in_row(nums_seq, q as int, v as int, r as int),
                    decreases row_len - r,
                {
                    proof {
                        assert(nums@[q as int]@[r as int] == nums_seq[q as int][r as int]);
                    }
                    if nums[q][r] == v {
                        assert(nums_seq[q as int][r as int] == v as int);
                        assert(Self::appears_in_row(nums_seq, q as int, v as int, (r + 1) as int));
                        found = true;
                    }
                    r = r + 1;
                }
                if !found {
                    assert(!Self::appears_in_row(nums_seq, q as int, v as int, nums_seq[q as int].len() as int));
                    proof { bad_row = q as int; }
                    all = false;
                } else {
                    assert(Self::appears_in_row(nums_seq, q as int, v as int, nums_seq[q as int].len() as int));
                    q = q + 1;
                }
            }

            if all {
                assert(Self::in_all_arrays(nums_seq, v as int, nums.len() as int));
                let ghost old_out = out@;
                out.push(v);
                proof {
                    assert(out@[old_out.len() as int] == v);
                    assert forall|u: int| 1 <= u <= v && #[trigger] Self::in_all_arrays(nums_seq, u, nums.len() as int) implies
                        exists|p: int| 0 <= p < out.len() && out[p] as int == u
                    by {
                        if u < v {
                            let p_old = choose|p: int| 0 <= p < old_out.len() && old_out[p] as int == u;
                            assert(out@[p_old] == old_out[p_old]);
                        } else {
                            assert(out@[old_out.len() as int] as int == v as int);
                        }
                    }
                }
            } else {
                assert(!Self::in_all_arrays(nums_seq, v as int, nums.len() as int));
            }
            v = v + 1;
        }
        out
    }
}

}
