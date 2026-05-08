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
        {
            let mut s: i32 = 0;
            let mut i: usize = 0;
            while i < nums1.len()
            {
                if nums1[i].len() == 2 && nums1[i][0] == id {
                    s = s + nums1[i][1];
                }
                i = i + 1;
            }

            let mut j: usize = 0;
            while j < nums2.len()
            {
                if nums2[j].len() == 2 && nums2[j][0] == id {
                    s = s + nums2[j][1];
                }
                j = j + 1;
            }

            if s > 0 {
                out.push(vec![id, s]);
            }
            id = id + 1;
        }

        out
    }
}

}
