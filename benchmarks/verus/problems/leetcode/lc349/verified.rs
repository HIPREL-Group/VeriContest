use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn no_duplicates(s: Seq<i32>) -> bool 
    {
        forall |i: int, j: int| 
            0 <= i < s.len() && 0 <= j < s.len() && i != j 
            ==> s[i] != s[j]
    }

    pub open spec fn is_intersection(seq1: Seq<i32>, seq2: Seq<i32>, res: Seq<i32>) -> bool 
    {
        (forall |x: i32| #[trigger] res.contains(x) ==> seq1.contains(x) && seq2.contains(x)) &&
        (forall |x: i32| (#[trigger] seq1.contains(x) && seq2.contains(x)) ==> res.contains(x)) &&
        Solution::no_duplicates(res)
    }

    pub fn intersection(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums1.len() <= 1000,
            1 <= nums2.len() <= 1000,
            forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1000,
            forall |i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 1000,
        ensures
            Solution::is_intersection(nums1@, nums2@, result@),
    {
        let mut result = Vec::new();
        let mut i = 0;

        while i < nums1.len()
            invariant
                i <= nums1.len(),
                Solution::no_duplicates(result@),
                forall |x: i32|
                    result@.contains(x) ==> nums1@.contains(x) && nums2@.contains(x),
                forall |p: int|
                    0 <= p < i && #[trigger] nums2@.contains(nums1@[p]) ==> #[trigger] result@.contains(nums1@[p]),
            decreases
                nums1.len() - i
        {
            let candidate = nums1[i];
            
            let mut j: usize = 0;
            let mut found_in_nums2: bool = false;
            
            while j < nums2.len()
                invariant
                    j <= nums2.len(),
                    found_in_nums2 ==> (exists |q: int| 0 <= q < j && nums2@[q] == candidate),
                    !found_in_nums2 ==> (forall |q: int| 0 <= q < j ==> nums2@[q] != candidate),
                decreases
                    nums2.len() - j
            {
                if nums2[j] == candidate {
                    found_in_nums2 = true;
                }
                j = j + 1;
            }

            assert(found_in_nums2 <==> nums2@.contains(candidate));

            if found_in_nums2 {
                let mut k = 0;
                let mut already_in_result = false;
                
                while k < result.len()
                    invariant
                        k <= result.len(),
                        already_in_result ==> (exists |r: int| 0 <= r < k && result@[r] == candidate),
                        !already_in_result ==> (forall |r: int| 0 <= r < k ==> result@[r] != candidate),
                    decreases
                        result.len() - k
                {
                    if result[k] == candidate {
                        already_in_result = true;
                    }
                    k = k + 1;
                }

                assert(already_in_result <==> result@.contains(candidate));

                if !already_in_result {
                    let ghost old_result = result@;
                    
                    result.push(candidate);
                    
                    assert forall |x: i32| #[trigger] old_result.contains(x) implies result@.contains(x) by {
                        if old_result.contains(x) {
                            let idx = choose |idx: int| 0 <= idx < old_result.len() && old_result[idx] == x;
                            assert(0 <= idx < result@.len());
                            assert(result@[idx] == x);
                        }
                    }
                    
                    
                    assert(result@[result@.len() - 1] == candidate);
                    assert(result@.contains(candidate));
                    
                    assert forall |p: int| 0 <= p < i && #[trigger] nums2@.contains(nums1@[p]) 
                        implies #[trigger] result@.contains(nums1@[p]) by {
                        if 0 <= p < i && nums2@.contains(nums1@[p]) {
                            assert(old_result.contains(nums1@[p])); 
                            assert(result@.contains(nums1@[p]));   
                        }
                    }
                }
                
                assert(result@.contains(candidate));
            }
            
            assert(nums2@.contains(nums1@[i as int]) ==> result@.contains(nums1@[i as int]));
            
            assert forall |p: int| 0 <= p < i + 1 && #[trigger] nums2@.contains(nums1@[p]) 
                implies #[trigger] result@.contains(nums1@[p]) by {
                if p < i {
                    
                } else {
                    
                    assert(nums2@.contains(nums1@[i as int]) ==> result@.contains(nums1@[i as int]));
                }
            }
            
            i = i + 1;
        }
        
        result
    }
}

} 