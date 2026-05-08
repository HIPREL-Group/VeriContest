use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn val_for_id_vec(arr: Seq<Vec<i32>>, id: int, end: int) -> int
    decreases end
{
    if end <= 0 { 0 }
    else if arr[end - 1]@[0] as int == id { arr[end - 1]@[1] as int + val_for_id_vec(arr, id, end - 1) }
    else { val_for_id_vec(arr, id, end - 1) }
}

pub open spec fn has_id_vec(arr: Seq<Vec<i32>>, id: int, end: int) -> bool
    decreases end
{
    if end <= 0 { false }
    else if arr[end - 1]@[0] as int == id { true }
    else { has_id_vec(arr, id, end - 1) }
}

impl Solution {
    pub fn merge_arrays(nums1: Vec<Vec<i32>>, nums2: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
        requires
            1 <= nums1.len() <= 200,
            1 <= nums2.len() <= 200,
            forall|i: int| 0 <= i < nums1.len() ==> #[trigger] nums1[i].len() == 2,
            forall|i: int| 0 <= i < nums2.len() ==> #[trigger] nums2[i].len() == 2,
            forall|i: int| 0 <= i < nums1.len() ==> 1 <= #[trigger] nums1[i][0] <= 1000 && 1 <= nums1[i][1] <= 1000,
            forall|i: int| 0 <= i < nums2.len() ==> 1 <= #[trigger] nums2[i][0] <= 1000 && 1 <= nums2[i][1] <= 1000,
        ensures
            forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == 2,
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i][0] < result[j][0],
            forall|p: int| 0 <= p < result.len() ==> result[p][1] as int == val_for_id_vec(nums1@, result[p][0] as int, nums1.len() as int) + val_for_id_vec(nums2@, result[p][0] as int, nums2.len() as int),
            forall|p: int| 0 <= p < result.len() ==> has_id_vec(nums1@, result[p][0] as int, nums1.len() as int) || has_id_vec(nums2@, result[p][0] as int, nums2.len() as int),
            forall|id: int| 1 <= id <= 1000 && (has_id_vec(nums1@, id, nums1.len() as int) || has_id_vec(nums2@, id, nums2.len() as int)) ==> exists|p: int| 0 <= p < result.len() && result[p][0] as int == id,
    {
        let mut out: Vec<Vec<i32>> = Vec::new();

        let mut id: i32 = 1;
        while id <= 1000
            invariant
                1 <= id <= 1001,
                forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i].len() == 2,
                forall|i: int, j: int| 0 <= i < j < out.len() ==> out[i][0] < out[j][0],
                forall|p: int| 0 <= p < out.len() ==> out[p][0] < id,
                forall|p: int| 0 <= p < out.len() ==> out[p][1] as int == val_for_id_vec(nums1@, out[p][0] as int, nums1.len() as int) + val_for_id_vec(nums2@, out[p][0] as int, nums2.len() as int),
                forall|p: int| 0 <= p < out.len() ==> has_id_vec(nums1@, out[p][0] as int, nums1.len() as int) || has_id_vec(nums2@, out[p][0] as int, nums2.len() as int),
                forall|k: int| 1 <= k < id && (has_id_vec(nums1@, k, nums1.len() as int) || has_id_vec(nums2@, k, nums2.len() as int)) ==> exists|p: int| 0 <= p < out.len() && out[p][0] as int == k,
                nums1.len() <= 200,
                nums2.len() <= 200,
                forall|i: int| 0 <= i < nums1.len() ==> #[trigger] nums1[i].len() == 2,
                forall|i: int| 0 <= i < nums2.len() ==> #[trigger] nums2[i].len() == 2,
                forall|i: int| 0 <= i < nums1.len() ==> 1 <= #[trigger] nums1[i][0] <= 1000 && 1 <= nums1[i][1] <= 1000,
                forall|i: int| 0 <= i < nums2.len() ==> 1 <= #[trigger] nums2[i][0] <= 1000 && 1 <= nums2[i][1] <= 1000,
            decreases 1001 - id,
        {
            let mut s: i32 = 0;
            let mut i: usize = 0;
            while i < nums1.len()
                invariant
                    0 <= i <= nums1.len(),
                    nums1.len() <= 200,
                    1 <= id <= 1000,
                    forall|k: int| 0 <= k < nums1.len() ==> #[trigger] nums1[k].len() == 2,
                    forall|k: int| 0 <= k < nums1.len() ==> 1 <= #[trigger] nums1[k][0] <= 1000 && 1 <= nums1[k][1] <= 1000,
                    s as int == val_for_id_vec(nums1@, id as int, i as int),
                    0 <= s as int <= 1000 * (i as int),
                    has_id_vec(nums1@, id as int, i as int) <==> s > 0,
                decreases nums1.len() - i,
            {
                if nums1[i].len() == 2 && nums1[i][0] == id {
                    s = s + nums1[i][1];
                }
                i = i + 1;
            }

            let mut j: usize = 0;
            while j < nums2.len()
                invariant
                    0 <= j <= nums2.len(),
                    nums2.len() <= 200,
                    nums1.len() <= 200,
                    1 <= id <= 1000,
                    forall|k: int| 0 <= k < nums2.len() ==> #[trigger] nums2[k].len() == 2,
                    forall|k: int| 0 <= k < nums2.len() ==> 1 <= #[trigger] nums2[k][0] <= 1000 && 1 <= nums2[k][1] <= 1000,
                    s as int == val_for_id_vec(nums1@, id as int, nums1.len() as int) + val_for_id_vec(nums2@, id as int, j as int),
                    0 <= s as int <= 1000 * (nums1.len() as int) + 1000 * (j as int),
                    (has_id_vec(nums1@, id as int, nums1.len() as int) || has_id_vec(nums2@, id as int, j as int)) <==> s > 0,
                decreases nums2.len() - j,
            {
                if nums2[j].len() == 2 && nums2[j][0] == id {
                    s = s + nums2[j][1];
                }
                j = j + 1;
            }

            if s > 0 {
                let ghost old_out = out@;
                let old_len = out.len();
                out.push(vec![id, s]);
                assert(out[old_len as int][0] == id);
                assert(out[old_len as int][1] == s);
                assert(out[old_len as int].len() == 2);
                assert(forall|p: int| 0 <= p < old_len as int ==> out@[p] === old_out[p]);
                proof {
                    assert forall|k: int| 1 <= k < id as int && (has_id_vec(nums1@, k, nums1.len() as int) || has_id_vec(nums2@, k, nums2.len() as int)) implies exists|p: int| 0 <= p < out.len() && #[trigger] out[p][0] as int == k by {
                        let pw = choose|p: int| 0 <= p < old_len as int && old_out[p]@[0] as int == k;
                        assert(0 <= pw < out.len());
                        assert(out@[pw] === old_out[pw]);
                        assert(out[pw][0] as int == k);
                    };
                }
            }
            id = id + 1;
        }

        out
    }
}

}
