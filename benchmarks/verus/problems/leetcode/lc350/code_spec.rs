use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn nat_min(a: nat, b: nat) -> nat {
        if a <= b { a } else { b }
    }

    pub open spec fn count_occ_prefix(s: Seq<i32>, n: nat, v: i32) -> nat
        recommends
            n <= s.len(),
        decreases n
    {
        if n == 0 {
            0nat
        } else {
            Solution::count_occ_prefix(s, (n - 1) as nat, v) + if s[(n - 1) as int] == v { 1nat } else { 0nat }
        }
    }

    pub open spec fn count_occ(s: Seq<i32>, v: i32) -> nat {
        Solution::count_occ_prefix(s, s.len() as nat, v)
    }

    pub fn intersect(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums1.len() <= 1000,
            1 <= nums2.len() <= 1000,
            forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1000,
            forall |i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 1000,
        ensures
            forall |v: int| 0 <= v <= 1000 ==> #[trigger] Solution::count_occ(result@, v as i32)
                == Solution::nat_min(Solution::count_occ(nums1@, v as i32), Solution::count_occ(nums2@, v as i32)),
            forall |i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000,
    {
        let mut freq1: Vec<i32> = Vec::new();
        let mut t: usize = 0;
        while t <= 1000 {
            freq1.push(0);
            t = t + 1;
        }
        let mut i: usize = 0;
        while i < nums1.len() {
            let idx: usize = nums1[i] as usize;
            freq1.set(idx, freq1[idx] + 1);
            i = i + 1;
        }

        let mut freq2: Vec<i32> = Vec::new();
        let mut t2: usize = 0;
        while t2 <= 1000 {
            freq2.push(0);
            t2 = t2 + 1;
        }
        let mut result: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < nums2.len() {
            let idx: usize = nums2[j] as usize;
            freq2.set(idx, freq2[idx] + 1);
            j = j + 1;
        }

        let mut v: usize = 0;
        while v <= 1000 {
            let mut c: i32 = if freq1[v] < freq2[v] { freq1[v] } else { freq2[v] };
            while c > 0 {
                result.push(v as i32);
                c = c - 1;
            }
            v = v + 1;
        }
        result
    }
}

}
