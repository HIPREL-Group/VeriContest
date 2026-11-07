use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn triplet_match(a: Seq<i32>, b: Seq<i32>, i: int, j: int, k: int) -> int {
    if a[i] as int * a[i] as int == b[j] as int * b[k] as int { 1 } else { 0 }
}

pub open spec fn count_k(a: Seq<i32>, b: Seq<i32>, i: int, j: int, k: int) -> int
    decreases b.len() - k
{
    if k >= b.len() { 0 }
    else { triplet_match(a, b, i, j, k) + count_k(a, b, i, j, k + 1) }
}

pub open spec fn count_j(a: Seq<i32>, b: Seq<i32>, i: int, j: int) -> int
    decreases b.len() - j
{
    if j >= b.len() { 0 }
    else { count_k(a, b, i, j, j + 1) + count_j(a, b, i, j + 1) }
}

pub open spec fn count_i(a: Seq<i32>, b: Seq<i32>, i: int) -> int
    decreases a.len() - i
{
    if i >= a.len() { 0 }
    else { count_j(a, b, i, 0) + count_i(a, b, i + 1) }
}

pub open spec fn count_triplets(nums1: Seq<i32>, nums2: Seq<i32>) -> int {
    count_i(nums1, nums2, 0) + count_i(nums2, nums1, 0)
}

impl Solution {
    pub fn num_triplets(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: i32)
        requires
            1 <= nums1.len() <= 1000,
            1 <= nums2.len() <= 1000,
            forall |i: int| 0 <= i < nums1.len() ==> 1 <= #[trigger] nums1[i] <= 100_000,
            forall |i: int| 0 <= i < nums2.len() ==> 1 <= #[trigger] nums2[i] <= 100_000,
        ensures
            result as int == count_triplets(nums1@, nums2@),
    {
        let n1 = nums1.len();
        let n2 = nums2.len();
        let mut count: i32 = 0;
        let mut i: usize = 0;
        while i < n1 {
            let mut j: usize = 0;
            while j < n2 {
                let mut k: usize = j + 1;
                while k < n2 {
                    if (nums1[i] as i64) * (nums1[i] as i64) == (nums2[j] as i64) * (nums2[k] as i64) {
                        count = count + 1;
                    }
                    k = k + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        let mut i2: usize = 0;
        while i2 < n2 {
            let mut j2: usize = 0;
            while j2 < n1 {
                let mut k2: usize = j2 + 1;
                while k2 < n1 {
                    if (nums2[i2] as i64) * (nums2[i2] as i64) == (nums1[j2] as i64) * (nums1[k2] as i64) {
                        count = count + 1;
                    }
                    k2 = k2 + 1;
                }
                j2 = j2 + 1;
            }
            i2 = i2 + 1;
        }
        count
    }
}

}
