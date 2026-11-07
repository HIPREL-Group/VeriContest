use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    proof fn lemma_filter_push<T>(seq: Seq<T>, x: T, f: spec_fn(T) -> bool)
        ensures
            seq.push(x).filter(f).len() == seq.filter(f).len() + if f(x) { 1 as nat } else { 0 as nat },
            seq.push(x).filter(f) =~= seq.filter(f) + (if f(x) { seq![x] } else { Seq::empty() }),
        decreases seq.len(),
    {
        reveal_with_fuel(Seq::filter, 2);

        if seq.len() == 0 {
        } else {
            let head = seq[0];
            let tail = seq.subrange(1, seq.len() as int);
            
            Self::lemma_filter_push(tail, x, f);

            assert(seq =~= seq![head] + tail);
            assert(seq.push(x) =~= seq![head] + tail.push(x));

            if f(head) {
                assert(seq.filter(f) =~= seq![head] + tail.filter(f));
                assert(seq.push(x).filter(f) =~= seq![head] + tail.push(x).filter(f));
            } else {
                assert(seq.filter(f) =~= tail.filter(f));
                assert(seq.push(x).filter(f) =~= tail.push(x).filter(f));
            }
        }
    }

    pub fn min_operations(nums: Vec<i32>, k: i32) -> (res: i32) 
        requires 
            1 <= nums.len() <= 50, 
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000, 
            1 <= k <= 1_000_000_000, 
            exists |i: int| 0 <= i < nums.len() && nums[i] >= k, 
        ensures 
            (res as int) == nums@.filter(|x: i32| x < k).len(),
            0 <= res <= nums.len(), 
    {
        let mut count: i32 = 0;
        for i in 0..nums.len() 
            invariant
                1 <= nums.len() <= 50, 
                forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000, 
                1 <= k <= 1_000_000_000, 
                exists |i: int| 0 <= i < nums.len() && nums[i] >= k, 
                count == nums@.subrange(0, i as int).filter(|x: i32| x < k).len(),
                0 <= count <= i,
        {
            proof {
                Self::lemma_filter_push(nums@.subrange(0, i as int), nums@[i as int], |x: i32| x < k);
                assert(nums@.subrange(0, i as int + 1) == nums@.subrange(0, i as int).push(nums@[i as int]));
            }
            
            if nums[i] < k {
                count += 1;
            }
        }
        
        assert(nums@.subrange(0, nums.len() as int) == nums@);
        
        return count;
    }
}

}