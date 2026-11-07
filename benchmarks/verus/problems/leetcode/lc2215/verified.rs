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

    pub open spec fn is_difference(nums1: Seq<i32>, nums2: Seq<i32>, result: Seq<Seq<i32>>) -> bool
    {
        result.len() == 2 &&
        (forall |x: i32| #[trigger] result[0].contains(x) ==> nums1.contains(x) && !nums2.contains(x)) &&
        (forall |x: i32| (#[trigger] nums1.contains(x) && !#[trigger] nums2.contains(x)) ==> result[0].contains(x)) &&
        Solution::no_duplicates(result[0]) &&
        (forall |x: i32| #[trigger] result[1].contains(x) ==> nums2.contains(x) && !nums1.contains(x)) &&
        (forall |x: i32| (#[trigger] nums2.contains(x) && !#[trigger] nums1.contains(x)) ==> result[1].contains(x)) &&
        Solution::no_duplicates(result[1])
    }

    pub fn find_difference(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: Vec<Vec<i32>>)
        requires
            1 <= nums1.len() <= 1000,
            1 <= nums2.len() <= 1000,
            forall |i: int| 0 <= i < nums1.len() ==> -1000 <= #[trigger] nums1[i] <= 1000,
            forall |j: int| 0 <= j < nums2.len() ==> -1000 <= #[trigger] nums2[j] <= 1000,
        ensures
            result.len() == 2,
            Solution::is_difference(nums1@, nums2@, seq![result[0]@, result[1]@]),
    {
        let mut diff1 = Vec::new();
        let mut i = 0;

        
        while i < nums1.len()
            invariant
                i <= nums1.len(),
                Solution::no_duplicates(diff1@),
                forall |x: i32| #[trigger] diff1@.contains(x) ==> nums1@.contains(x) && !nums2@.contains(x),
                forall |p: int| 0 <= p < i && nums1@.contains(nums1@[p]) && !nums2@.contains(nums1@[p])
                    ==> #[trigger] diff1@.contains(nums1@[p]),
            decreases
                nums1.len() - i
        {
            let candidate = nums1[i];

            let mut j = 0;
            let mut found_in_nums2 = false;

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

            
            if !found_in_nums2 {
                let mut k = 0;
                let mut already_in_diff1 = false;

                while k < diff1.len()
                    invariant
                        k <= diff1.len(),
                        already_in_diff1 ==> (exists |r: int| 0 <= r < k && diff1@[r] == candidate),
                        !already_in_diff1 ==> (forall |r: int| 0 <= r < k ==> diff1@[r] != candidate),
                    decreases
                        diff1.len() - k
                {
                    if diff1[k] == candidate {
                        already_in_diff1 = true;
                    }
                    k = k + 1;
                }

                assert(already_in_diff1 <==> diff1@.contains(candidate));

                if !already_in_diff1 {
                    let ghost old_diff1 = diff1@;

                    diff1.push(candidate);

                    
                    assert forall |x: i32| #[trigger] old_diff1.contains(x) implies diff1@.contains(x) by {
                        if old_diff1.contains(x) {
                            let idx = choose |idx: int| 0 <= idx < old_diff1.len() && old_diff1[idx] == x;
                            assert(0 <= idx < diff1@.len());
                            assert(diff1@[idx] == x);
                        }
                    }

                    assert(diff1@[diff1@.len() - 1] == candidate);
                    assert(diff1@.contains(candidate));

                    assert forall |x: i32| #[trigger] diff1@.contains(x) implies nums1@.contains(x) && !nums2@.contains(x) by {
                        if diff1@.contains(x) {
                            if old_diff1.contains(x) {
                            } else {
                                assert(x == candidate);
                                assert(nums1@.contains(candidate));
                                assert(!nums2@.contains(candidate));
                            }
                        }
                    }

                    assert forall |p: int| 0 <= p < i && nums1@.contains(nums1@[p]) && !nums2@.contains(nums1@[p])
                        implies #[trigger] diff1@.contains(nums1@[p]) by {
                        if 0 <= p < i && nums1@.contains(nums1@[p]) && !nums2@.contains(nums1@[p]) {
                            assert(old_diff1.contains(nums1@[p]));
                            assert(diff1@.contains(nums1@[p]));
                        }
                    }
                }

                assert(diff1@.contains(candidate));
            }

            assert(nums1@.contains(nums1@[i as int]) && !nums2@.contains(nums1@[i as int]) ==> diff1@.contains(nums1@[i as int]));

            assert forall |p: int| 0 <= p < i + 1 && nums1@.contains(nums1@[p]) && !nums2@.contains(nums1@[p])
                implies #[trigger] diff1@.contains(nums1@[p]) by {
                if p < i {
                    
                } else {
                    
                    assert(nums1@.contains(nums1@[i as int]) && !nums2@.contains(nums1@[i as int]) ==> diff1@.contains(nums1@[i as int]));
                }
            }

            i = i + 1;
        }

        
        let mut diff2 = Vec::new();
        let mut i2 = 0;

        while i2 < nums2.len()
            invariant
                i2 <= nums2.len(),
                Solution::no_duplicates(diff2@),
                forall |x: i32| #[trigger] diff2@.contains(x) ==> nums2@.contains(x) && !nums1@.contains(x),
                forall |p: int| 0 <= p < i2 && nums2@.contains(nums2@[p]) && !nums1@.contains(nums2@[p])
                    ==> #[trigger] diff2@.contains(nums2@[p]),
            decreases
                nums2.len() - i2
        {
            let candidate = nums2[i2];

            let mut j = 0;
            let mut found_in_nums1 = false;

            while j < nums1.len()
                invariant
                    j <= nums1.len(),
                    found_in_nums1 ==> (exists |q: int| 0 <= q < j && nums1@[q] == candidate),
                    !found_in_nums1 ==> (forall |q: int| 0 <= q < j ==> nums1@[q] != candidate),
                decreases
                    nums1.len() - j
            {
                if nums1[j] == candidate {
                    found_in_nums1 = true;
                }
                j = j + 1;
            }

            assert(found_in_nums1 <==> nums1@.contains(candidate));

            if !found_in_nums1 {
                let mut k = 0;
                let mut already_in_diff2 = false;

                while k < diff2.len()
                    invariant
                        k <= diff2.len(),
                        already_in_diff2 ==> (exists |r: int| 0 <= r < k && diff2@[r] == candidate),
                        !already_in_diff2 ==> (forall |r: int| 0 <= r < k ==> diff2@[r] != candidate),
                    decreases
                        diff2.len() - k
                {
                    if diff2[k] == candidate {
                        already_in_diff2 = true;
                    }
                    k = k + 1;
                }

                assert(already_in_diff2 <==> diff2@.contains(candidate));

                if !already_in_diff2 {
                    let ghost old_diff2 = diff2@;

                    diff2.push(candidate);

                    assert forall |x: i32| #[trigger] old_diff2.contains(x) implies diff2@.contains(x) by {
                        if old_diff2.contains(x) {
                            let idx = choose |idx: int| 0 <= idx < old_diff2.len() && old_diff2[idx] == x;
                            assert(0 <= idx < diff2@.len());
                            assert(diff2@[idx] == x);
                        }
                    }

                    assert(diff2@[diff2@.len() - 1] == candidate);
                    assert(diff2@.contains(candidate));

                    assert forall |x: i32| #[trigger] diff2@.contains(x) implies nums2@.contains(x) && !nums1@.contains(x) by {
                        if diff2@.contains(x) {
                            if old_diff2.contains(x) {
                            } else {
                                assert(x == candidate);
                                assert(nums2@.contains(candidate));
                                assert(!nums1@.contains(candidate));
                            }
                        }
                    }

                    assert forall |p: int| 0 <= p < i2 && nums2@.contains(nums2@[p]) && !nums1@.contains(nums2@[p])
                        implies #[trigger] diff2@.contains(nums2@[p]) by {
                        if 0 <= p < i2 && nums2@.contains(nums2@[p]) && !nums1@.contains(nums2@[p]) {
                            assert(old_diff2.contains(nums2@[p]));
                            assert(diff2@.contains(nums2@[p]));
                        }
                    }
                }

                assert(diff2@.contains(candidate));
            }

            assert(nums2@.contains(nums2@[i2 as int]) && !nums1@.contains(nums2@[i2 as int]) ==> diff2@.contains(nums2@[i2 as int]));

            assert forall |p: int| 0 <= p < i2 + 1 && nums2@.contains(nums2@[p]) && !nums1@.contains(nums2@[p])
                implies #[trigger] diff2@.contains(nums2@[p]) by {
                if p < i2 {
                } else {
                    assert(nums2@.contains(nums2@[i2 as int]) && !nums1@.contains(nums2@[i2 as int]) ==> diff2@.contains(nums2@[i2 as int]));
                }
            }

            i2 = i2 + 1;
        }

        let mut result = Vec::new();
        result.push(diff1);
        result.push(diff2);

        assert(result.len() == 2);
        assert(result[0]@ == diff1@);
        assert(result[1]@ == diff2@);

        assert(Solution::is_difference(nums1@, nums2@, seq![result[0]@, result[1]@]));

        result
    }
}

} 
