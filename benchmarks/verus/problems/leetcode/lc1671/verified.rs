use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;


pub open spec fn is_inc_subseq_ending_at(nums: Seq<i32>, indices: Seq<int>, i: int) -> bool {
    &&& indices.len() >= 1
    &&& indices[indices.len() - 1] == i
    &&& (forall |k: int| 0 <= k < indices.len() ==> 0 <= (#[trigger] indices[k]) < nums.len())
    &&& (forall |k: int| 0 <= k < indices.len() - 1 ==>
        indices[k] < indices[k + 1] && (#[trigger] nums[indices[k]]) < nums[indices[k + 1]])
}


pub open spec fn is_dec_subseq_starting_at(nums: Seq<i32>, indices: Seq<int>, i: int) -> bool {
    &&& indices.len() >= 1
    &&& indices[0] == i
    &&& (forall |k: int| 0 <= k < indices.len() ==> 0 <= (#[trigger] indices[k]) < nums.len())
    &&& (forall |k: int| 0 <= k < indices.len() - 1 ==>
        indices[k] < indices[k + 1] && (#[trigger] nums[indices[k]]) > nums[indices[k + 1]])
}

impl Solution {
    pub open spec fn is_mountain_subseq(nums: Seq<i32>, indices: Seq<int>, peak: int) -> bool {
        &&& indices.len() >= 3
        &&& 0 < peak < indices.len() - 1
        &&& (forall |k: int| 0 <= k < indices.len() ==> 0 <= (#[trigger] indices[k]) < nums.len())
        &&& (forall |k: int| 0 <= k < peak ==>
            indices[k] < indices[k + 1] && (#[trigger] nums[indices[k]]) < nums[indices[k + 1]])
        &&& (forall |k: int| peak <= k < indices.len() - 1 ==>
            indices[k] < indices[k + 1] && (#[trigger] nums[indices[k]]) > nums[indices[k + 1]])
    }

    
    pub open spec fn lis_max_scan(nums: Seq<i32>, idx: int, bound: int) -> int
        decreases idx, bound
    {
        if bound <= 0 { 0 }
        else {
            let rest = Self::lis_max_scan(nums, idx, bound - 1);
            if bound - 1 < idx && nums[bound - 1] < nums[idx] {
                let v = Self::lis_at(nums, bound - 1);
                if v > rest { v } else { rest }
            } else {
                rest
            }
        }
    }

    pub open spec fn lis_at(nums: Seq<i32>, i: int) -> int
        decreases i, i + 1
    {
        if i <= 0 { 1 }
        else {
            1 + Self::lis_max_scan(nums, i, i)
        }
    }

    pub open spec fn lds_max_scan(nums: Seq<i32>, idx: int, bound: int) -> int
        decreases nums.len() - idx, bound - idx
    {
        if bound <= idx || bound >= nums.len() as int { 0 }
        else {
            let rest = Self::lds_max_scan(nums, idx, bound - 1);
            if nums[bound] < nums[idx] {
                let v = Self::lds_at(nums, bound);
                if v > rest { v } else { rest }
            } else {
                rest
            }
        }
    }

    pub open spec fn lds_at(nums: Seq<i32>, i: int) -> int
        decreases nums.len() - i, nums.len() - i + 1
    {
        if i < 0 || i >= nums.len() as int - 1 { 1 }
        else {
            1 + Self::lds_max_scan(nums, i, nums.len() as int - 1)
        }
    }

    pub open spec fn mountain_len_at(nums: Seq<i32>, i: int) -> int {
        let lis = Self::lis_at(nums, i);
        let lds = Self::lds_at(nums, i);
        if lis > 1 && lds > 1 { lis + lds - 1 } else { 0 }
    }

    pub open spec fn max_mountain_len(nums: Seq<i32>, i: int) -> int
        decreases i + 1
    {
        if i < 0 { 0 }
        else {
            let cur = Self::mountain_len_at(nums, i);
            let rest = Self::max_mountain_len(nums, i - 1);
            if cur > rest { cur } else { rest }
        }
    }

    pub open spec fn min_removals(nums: Seq<i32>) -> int {
        nums.len() as int - Self::max_mountain_len(nums, nums.len() as int - 1)
    }

    

    proof fn lemma_lis_max_scan_nonneg(nums: Seq<i32>, idx: int, bound: int)
        ensures Self::lis_max_scan(nums, idx, bound) >= 0,
        decreases idx, bound,
    {
        reveal_with_fuel(Solution::lis_max_scan, 2);
        if bound > 0 {
            Self::lemma_lis_max_scan_nonneg(nums, idx, bound - 1);
            if bound - 1 < idx && bound - 1 >= 0 && (bound - 1) < nums.len()
                && idx < nums.len() && nums[bound - 1] < nums[idx] {
                Self::lemma_lis_at_pos(nums, bound - 1);
            }
        }
    }

    proof fn lemma_lis_at_pos(nums: Seq<i32>, i: int)
        requires 0 <= i < nums.len(),
        ensures Self::lis_at(nums, i) >= 1,
        decreases i, i + 1,
    {
        reveal_with_fuel(Solution::lis_at, 2);
        if i > 0 {
            Self::lemma_lis_max_scan_nonneg(nums, i, i);
        }
    }

    proof fn lemma_lis_max_scan_bound(nums: Seq<i32>, idx: int, bound: int)
        requires 0 <= idx < nums.len(), 0 <= bound <= idx,
        ensures Self::lis_max_scan(nums, idx, bound) <= idx,
        decreases idx, bound,
    {
        reveal_with_fuel(Solution::lis_max_scan, 2);
        if bound > 0 {
            Self::lemma_lis_max_scan_bound(nums, idx, bound - 1);
            if bound - 1 < idx && nums[bound - 1] < nums[idx] {
                Self::lemma_lis_at_bound(nums, bound - 1);
            }
        }
    }

    proof fn lemma_lis_at_bound(nums: Seq<i32>, i: int)
        requires 0 <= i < nums.len(),
        ensures Self::lis_at(nums, i) <= i + 1,
        decreases i, i + 1,
    {
        reveal_with_fuel(Solution::lis_at, 2);
        if i > 0 {
            Self::lemma_lis_max_scan_bound(nums, i, i);
        }
    }

    proof fn lemma_lis_max_scan_includes(nums: Seq<i32>, idx: int, bound: int, j: int)
        requires
            0 <= j < bound,
            j < idx,
            0 <= idx < nums.len(),
            0 < bound <= idx,
            nums[j] < nums[idx],
        ensures
            Self::lis_max_scan(nums, idx, bound) >= Self::lis_at(nums, j),
        decreases idx, bound,
    {
        reveal_with_fuel(Solution::lis_max_scan, 2);
        if j == bound - 1 {
            Self::lemma_lis_max_scan_nonneg(nums, idx, bound - 1);
        } else {
            Self::lemma_lis_max_scan_includes(nums, idx, bound - 1, j);
            if bound - 1 < idx && nums[bound - 1] < nums[idx] {
                Self::lemma_lis_at_pos(nums, bound - 1);
            }
        }
    }

    proof fn lemma_lis_max_scan_witness(nums: Seq<i32>, idx: int, bound: int) -> (j: int)
        requires
            0 <= idx < nums.len(),
            0 <= bound <= idx,
            Self::lis_max_scan(nums, idx, bound) > 0,
        ensures
            0 <= j < bound,
            j < idx,
            nums[j] < nums[idx],
            Self::lis_at(nums, j) == Self::lis_max_scan(nums, idx, bound),
        decreases idx, bound,
    {
        reveal_with_fuel(Solution::lis_max_scan, 2);
        let rest = Self::lis_max_scan(nums, idx, bound - 1);
        if bound - 1 < idx && nums[bound - 1] < nums[idx] {
            let v = Self::lis_at(nums, bound - 1);
            if v > rest {
                bound - 1
            } else if rest > 0 {
                Self::lemma_lis_max_scan_witness(nums, idx, bound - 1)
            } else {
                bound - 1
            }
        } else {
            Self::lemma_lis_max_scan_witness(nums, idx, bound - 1)
        }
    }

    proof fn lemma_extend_inc_subseq(nums: Seq<i32>, w: Seq<int>, new_idx: int)
        requires
            w.len() >= 1,
            is_inc_subseq_ending_at(nums, w, w[w.len() - 1]),
            0 <= new_idx < nums.len(),
            w[w.len() - 1] < new_idx,
            nums[w[w.len() - 1]] < nums[new_idx],
        ensures
            is_inc_subseq_ending_at(nums, w.push(new_idx), new_idx),
    {
        let ext = w.push(new_idx);
        assert forall |k: int| 0 <= k < ext.len() implies
            0 <= (#[trigger] ext[k]) < nums.len() by {
            if k < w.len() as int { assert(ext[k] == w[k]); }
            else { assert(ext[k] == new_idx); }
        }
        
        assert forall |k: int| 0 <= k < ext.len() - 1 implies
            (#[trigger] ext[k]) < ext[k + 1] by {
            if k < w.len() as int - 1 {
                assert(ext[k] == w[k]);
                assert(ext[k + 1] == w[k + 1]);
                
                assert(nums[w[k]] < nums[w[k + 1]]);
            } else {
                assert(ext[k] == w[w.len() - 1]);
                assert(ext[k + 1] == new_idx);
            }
        }
        
        assert forall |k: int| 0 <= k < ext.len() - 1 implies
            (#[trigger] nums[ext[k]]) < nums[ext[k + 1]] by {
            if k < w.len() as int - 1 {
                assert(ext[k] == w[k]);
                assert(ext[k + 1] == w[k + 1]);
                assert(nums[w[k]] < nums[w[k + 1]]);
            } else {
                assert(ext[k] == w[w.len() - 1]);
                assert(ext[k + 1] == new_idx);
            }
        }
        
        assert forall |k: int| 0 <= k < ext.len() - 1 implies
            ext[k] < ext[k + 1]
            && (#[trigger] nums[ext[k]]) < nums[ext[k + 1]] by {
            assert(ext[k] < ext[k + 1]);
            assert(nums[ext[k]] < nums[ext[k + 1]]);
        }
    }

    proof fn lemma_lis_achievable(nums: Seq<i32>, i: int) -> (w: Seq<int>)
        requires 0 <= i < nums.len(),
        ensures
            is_inc_subseq_ending_at(nums, w, i),
            w.len() == Self::lis_at(nums, i),
        decreases i, i + 1,
    {
        reveal_with_fuel(Solution::lis_at, 2);
        if i <= 0 {
            let w: Seq<int> = seq![i];
            assert(is_inc_subseq_ending_at(nums, w, i));
            w
        } else {
            Self::lemma_lis_max_scan_nonneg(nums, i, i);
            let mlb = Self::lis_max_scan(nums, i, i);
            if mlb == 0 {
                let w: Seq<int> = seq![i];
                assert(is_inc_subseq_ending_at(nums, w, i));
                w
            } else {
                let j = Self::lemma_lis_max_scan_witness(nums, i, i);
                let prev_w = Self::lemma_lis_achievable(nums, j);
                Self::lemma_extend_inc_subseq(nums, prev_w, i);
                prev_w.push(i)
            }
        }
    }

    proof fn lemma_lis_optimal(nums: Seq<i32>, i: int, indices: Seq<int>)
        requires
            is_inc_subseq_ending_at(nums, indices, i),
            0 <= i < nums.len(),
        ensures
            indices.len() <= Self::lis_at(nums, i),
        decreases indices.len(),
    {
        reveal_with_fuel(Solution::lis_at, 2);
        Self::lemma_lis_at_pos(nums, i);
        if indices.len() > 1 {
            let prev_idx = indices[indices.len() - 2];
            let prev_seq = indices.subrange(0, indices.len() - 1);
            assert(prev_seq[prev_seq.len() - 1] == prev_idx);
            assert forall |k: int| 0 <= k < prev_seq.len() implies
                0 <= (#[trigger] prev_seq[k]) < nums.len() by {
                assert(prev_seq[k] == indices[k]);
            }
            
            assert forall |k: int| 0 <= k < prev_seq.len() - 1 implies
                (#[trigger] prev_seq[k]) < prev_seq[k + 1] by {
                assert(prev_seq[k] == indices[k]);
                assert(prev_seq[k + 1] == indices[k + 1]);
                assert(nums[indices[k]] < nums[indices[k + 1]]);
            }
            assert forall |k: int| 0 <= k < prev_seq.len() - 1 implies
                (#[trigger] nums[prev_seq[k]]) < nums[prev_seq[k + 1]] by {
                assert(prev_seq[k] == indices[k]);
                assert(prev_seq[k + 1] == indices[k + 1]);
            }
            assert forall |k: int| 0 <= k < prev_seq.len() - 1 implies
                prev_seq[k] < prev_seq[k + 1]
                && (#[trigger] nums[prev_seq[k]]) < nums[prev_seq[k + 1]] by {
                assert(prev_seq[k] < prev_seq[k + 1]);
                assert(nums[prev_seq[k]] < nums[prev_seq[k + 1]]);
            }
            assert(is_inc_subseq_ending_at(nums, prev_seq, prev_idx));
            Self::lemma_lis_optimal(nums, prev_idx, prev_seq);
            assert(indices[indices.len() - 2] < indices[indices.len() - 1]);
            assert(nums[indices[indices.len() - 2]] < nums[indices[indices.len() - 1]]);
            Self::lemma_lis_max_scan_includes(nums, i, i, prev_idx);
        }
    }

    

    proof fn lemma_lds_max_scan_nonneg(nums: Seq<i32>, idx: int, bound: int)
        requires 0 <= idx < nums.len(),
        ensures Self::lds_max_scan(nums, idx, bound) >= 0,
        decreases nums.len() - idx, bound - idx,
    {
        reveal_with_fuel(Solution::lds_max_scan, 2);
        if bound > idx && bound < nums.len() as int {
            Self::lemma_lds_max_scan_nonneg(nums, idx, bound - 1);
            if nums[bound] < nums[idx] {
                Self::lemma_lds_at_pos(nums, bound);
            }
        }
    }

    proof fn lemma_lds_at_pos(nums: Seq<i32>, i: int)
        requires 0 <= i < nums.len(),
        ensures Self::lds_at(nums, i) >= 1,
        decreases nums.len() - i, nums.len() - i + 1,
    {
        reveal_with_fuel(Solution::lds_at, 2);
        if i < nums.len() as int - 1 {
            Self::lemma_lds_max_scan_nonneg(nums, i, nums.len() as int - 1);
        }
    }

    proof fn lemma_lds_max_scan_bound(nums: Seq<i32>, idx: int, bound: int)
        requires 0 <= idx < nums.len(), idx < bound, bound < nums.len() as int,
        ensures Self::lds_max_scan(nums, idx, bound) <= nums.len() - 1 - idx,
        decreases nums.len() - idx, bound - idx,
    {
        reveal_with_fuel(Solution::lds_max_scan, 2);
        if bound > idx && bound < nums.len() as int {
            if bound - 1 > idx {
                Self::lemma_lds_max_scan_bound(nums, idx, bound - 1);
            }
            if nums[bound] < nums[idx] {
                Self::lemma_lds_at_bound(nums, bound);
            }
        }
    }

    proof fn lemma_lds_at_bound(nums: Seq<i32>, i: int)
        requires 0 <= i < nums.len(),
        ensures Self::lds_at(nums, i) <= nums.len() - i,
        decreases nums.len() - i, nums.len() - i + 1,
    {
        reveal_with_fuel(Solution::lds_at, 2);
        if i < nums.len() as int - 1 {
            Self::lemma_lds_max_scan_bound(nums, i, nums.len() as int - 1);
        }
    }

    proof fn lemma_lds_max_scan_includes(nums: Seq<i32>, idx: int, bound: int, j: int)
        requires
            idx < j,
            j <= bound,
            0 <= idx < nums.len(),
            bound < nums.len() as int,
            nums[j] < nums[idx],
        ensures
            Self::lds_max_scan(nums, idx, bound) >= Self::lds_at(nums, j),
        decreases nums.len() - idx, bound - idx,
    {
        reveal_with_fuel(Solution::lds_max_scan, 2);
        if j == bound {
            if bound - 1 > idx {
                Self::lemma_lds_max_scan_nonneg(nums, idx, bound - 1);
            }
        } else {
            Self::lemma_lds_max_scan_includes(nums, idx, bound - 1, j);
            if nums[bound] < nums[idx] {
                Self::lemma_lds_at_pos(nums, bound);
            }
        }
    }

    proof fn lemma_lds_max_scan_witness(nums: Seq<i32>, idx: int, bound: int) -> (j: int)
        requires
            0 <= idx < nums.len(),
            idx < bound,
            bound < nums.len() as int,
            Self::lds_max_scan(nums, idx, bound) > 0,
        ensures
            idx < j <= bound,
            j < nums.len(),
            nums[j] < nums[idx],
            Self::lds_at(nums, j) == Self::lds_max_scan(nums, idx, bound),
        decreases nums.len() - idx, bound - idx,
    {
        reveal_with_fuel(Solution::lds_max_scan, 2);
        let rest = if bound - 1 > idx { Self::lds_max_scan(nums, idx, bound - 1) } else { 0 };
        if nums[bound] < nums[idx] {
            let v = Self::lds_at(nums, bound);
            if v > rest {
                bound
            } else if rest > 0 && bound - 1 > idx {
                Self::lemma_lds_max_scan_witness(nums, idx, bound - 1)
            } else {
                bound
            }
        } else {
            Self::lemma_lds_max_scan_witness(nums, idx, bound - 1)
        }
    }

    proof fn lemma_prepend_dec_subseq(nums: Seq<i32>, w: Seq<int>, new_idx: int)
        requires
            w.len() >= 1,
            is_dec_subseq_starting_at(nums, w, w[0]),
            0 <= new_idx < nums.len(),
            new_idx < w[0],
            nums[new_idx] > nums[w[0]],
        ensures
            is_dec_subseq_starting_at(nums, seq![new_idx] + w, new_idx),
    {
        let ext = seq![new_idx] + w;
        assert forall |k: int| 0 <= k < ext.len() implies
            0 <= (#[trigger] ext[k]) < nums.len() by {
            if k == 0 { assert(ext[k] == new_idx); }
            else { assert(ext[k] == w[k - 1]); }
        }
        assert forall |k: int| 0 <= k < ext.len() - 1 implies
            (#[trigger] ext[k]) < ext[k + 1] by {
            if k == 0 {
                assert(ext[0] == new_idx);
                assert(ext[1] == w[0]);
            } else {
                assert(ext[k] == w[k - 1]);
                assert(ext[k + 1] == w[k]);
                assert(nums[w[k - 1]] > nums[w[k]]);
            }
        }
        assert forall |k: int| 0 <= k < ext.len() - 1 implies
            (#[trigger] nums[ext[k]]) > nums[ext[k + 1]] by {
            if k == 0 {
                assert(ext[0] == new_idx);
                assert(ext[1] == w[0]);
            } else {
                assert(ext[k] == w[k - 1]);
                assert(ext[k + 1] == w[k]);
            }
        }
        assert forall |k: int| 0 <= k < ext.len() - 1 implies
            ext[k] < ext[k + 1]
            && (#[trigger] nums[ext[k]]) > nums[ext[k + 1]] by {
            assert(ext[k] < ext[k + 1]);
            assert(nums[ext[k]] > nums[ext[k + 1]]);
        }
    }

    proof fn lemma_lds_achievable(nums: Seq<i32>, i: int) -> (w: Seq<int>)
        requires 0 <= i < nums.len(),
        ensures
            is_dec_subseq_starting_at(nums, w, i),
            w.len() == Self::lds_at(nums, i),
        decreases nums.len() - i, nums.len() - i + 1,
    {
        reveal_with_fuel(Solution::lds_at, 2);
        if i >= nums.len() as int - 1 {
            let w: Seq<int> = seq![i];
            assert(is_dec_subseq_starting_at(nums, w, i));
            w
        } else {
            Self::lemma_lds_max_scan_nonneg(nums, i, nums.len() as int - 1);
            let mds = Self::lds_max_scan(nums, i, nums.len() as int - 1);
            if mds == 0 {
                let w: Seq<int> = seq![i];
                assert(is_dec_subseq_starting_at(nums, w, i));
                w
            } else {
                let j = Self::lemma_lds_max_scan_witness(nums, i, nums.len() as int - 1);
                let next_w = Self::lemma_lds_achievable(nums, j);
                Self::lemma_prepend_dec_subseq(nums, next_w, i);
                seq![i] + next_w
            }
        }
    }

    proof fn lemma_lds_optimal(nums: Seq<i32>, i: int, indices: Seq<int>)
        requires
            is_dec_subseq_starting_at(nums, indices, i),
            0 <= i < nums.len(),
        ensures
            indices.len() <= Self::lds_at(nums, i),
        decreases indices.len(),
    {
        reveal_with_fuel(Solution::lds_at, 2);
        Self::lemma_lds_at_pos(nums, i);
        if indices.len() > 1 {
            let next_idx = indices[1];
            let rest_seq = indices.subrange(1, indices.len() as int);
            assert(rest_seq[0] == next_idx);
            assert forall |k: int| 0 <= k < rest_seq.len() implies
                0 <= (#[trigger] rest_seq[k]) < nums.len() by {
                assert(rest_seq[k] == indices[k + 1]);
            }
            assert forall |k: int| 0 <= k < rest_seq.len() - 1 implies
                (#[trigger] rest_seq[k]) < rest_seq[k + 1] by {
                assert(rest_seq[k] == indices[k + 1]);
                assert(rest_seq[k + 1] == indices[k + 2]);
                assert(nums[indices[k + 1]] > nums[indices[k + 2]]);
            }
            assert forall |k: int| 0 <= k < rest_seq.len() - 1 implies
                (#[trigger] nums[rest_seq[k]]) > nums[rest_seq[k + 1]] by {
                assert(rest_seq[k] == indices[k + 1]);
                assert(rest_seq[k + 1] == indices[k + 2]);
            }
            assert forall |k: int| 0 <= k < rest_seq.len() - 1 implies
                rest_seq[k] < rest_seq[k + 1]
                && (#[trigger] nums[rest_seq[k]]) > nums[rest_seq[k + 1]] by {
                assert(rest_seq[k] < rest_seq[k + 1]);
                assert(nums[rest_seq[k]] > nums[rest_seq[k + 1]]);
            }
            assert(is_dec_subseq_starting_at(nums, rest_seq, next_idx));
            Self::lemma_lds_optimal(nums, next_idx, rest_seq);
            assert(indices[0] < indices[1]);
            assert(nums[indices[0]] > nums[indices[1]]);
            Self::lemma_lds_max_scan_includes(nums, i, nums.len() as int - 1, next_idx);
        }
    }

    

    proof fn lemma_max_mountain_len_nonneg(nums: Seq<i32>, i: int)
        ensures Self::max_mountain_len(nums, i) >= 0,
        decreases i + 1,
    {
        reveal_with_fuel(Solution::max_mountain_len, 2);
        if i >= 0 {
            Self::lemma_max_mountain_len_nonneg(nums, i - 1);
        }
    }

    proof fn lemma_max_mountain_len_witness(nums: Seq<i32>, i: int) -> (p: int)
        requires
            Self::max_mountain_len(nums, i) > 0,
            0 <= i < nums.len(),
        ensures
            0 <= p <= i,
            Self::mountain_len_at(nums, p) == Self::max_mountain_len(nums, i),
        decreases i + 1,
    {
        reveal_with_fuel(Solution::max_mountain_len, 2);
        let cur = Self::mountain_len_at(nums, i);
        let rest = Self::max_mountain_len(nums, i - 1);
        Self::lemma_max_mountain_len_nonneg(nums, i - 1);
        if cur >= rest {
            if cur > 0 {
                i
            } else {
                
                assert(Self::max_mountain_len(nums, i) == cur);
                i
            }
        } else {
            
            if i > 0 {
                Self::lemma_max_mountain_len_witness(nums, i - 1)
            } else {
                
                
                i
            }
        }
    }

    proof fn lemma_max_mountain_len_includes(nums: Seq<i32>, i: int, p: int)
        requires 0 <= p <= i,
        ensures Self::max_mountain_len(nums, i) >= Self::mountain_len_at(nums, p),
        decreases i + 1,
    {
        reveal_with_fuel(Solution::max_mountain_len, 2);
        if p == i {
            Self::lemma_max_mountain_len_nonneg(nums, i - 1);
        } else if i >= 0 {
            Self::lemma_max_mountain_len_includes(nums, i - 1, p);
        }
    }

    proof fn lemma_mountain_achievable(nums: Seq<i32>, n: int)
        requires
            n == nums.len(),
            n >= 3,
            Self::max_mountain_len(nums, n - 1) >= 3,
        ensures
            exists |indices: Seq<int>, peak: int| Self::is_mountain_subseq(nums, indices, peak)
                && indices.len() == Self::max_mountain_len(nums, n - 1),
    {
        let p = Self::lemma_max_mountain_len_witness(nums, n - 1);
        let lis_len = Self::lis_at(nums, p);
        let lds_len = Self::lds_at(nums, p);
        assert(lis_len > 1 && lds_len > 1);
        assert(Self::mountain_len_at(nums, p) == lis_len + lds_len - 1);

        let inc_w = Self::lemma_lis_achievable(nums, p);
        let dec_w = Self::lemma_lds_achievable(nums, p);

        
        let dec_tail = dec_w.subrange(1, dec_w.len() as int);
        let mountain = inc_w + dec_tail;
        let peak_pos = (inc_w.len() - 1) as int;

        assert(mountain.len() == lis_len + lds_len - 1);

        assert forall |k: int| 0 <= k < mountain.len() implies
            0 <= (#[trigger] mountain[k]) < nums.len() by {
            if k < inc_w.len() as int {
                assert(mountain[k] == inc_w[k]);
            } else {
                let dk = k - inc_w.len() as int;
                assert(mountain[k] == dec_tail[dk]);
                assert(dec_tail[dk] == dec_w[dk + 1]);
            }
        }

        
        assert forall |k: int| 0 <= k < peak_pos implies
            (#[trigger] mountain[k]) < mountain[k + 1] by {
            assert(mountain[k] == inc_w[k]);
            assert(mountain[k + 1] == inc_w[k + 1]);
            assert(nums[inc_w[k]] < nums[inc_w[k + 1]]);
        }
        assert forall |k: int| 0 <= k < peak_pos implies
            (#[trigger] nums[mountain[k]]) < nums[mountain[k + 1]] by {
            assert(mountain[k] == inc_w[k]);
            assert(mountain[k + 1] == inc_w[k + 1]);
        }
        assert forall |k: int| 0 <= k < peak_pos implies
            mountain[k] < mountain[k + 1]
            && (#[trigger] nums[mountain[k]]) < nums[mountain[k + 1]] by {
            assert(mountain[k] < mountain[k + 1]);
            assert(nums[mountain[k]] < nums[mountain[k + 1]]);
        }

        
        assert forall |k: int| peak_pos <= k < mountain.len() - 1 implies
            (#[trigger] mountain[k]) < mountain[k + 1] by {
            if k == peak_pos {
                assert(mountain[k] == inc_w[inc_w.len() - 1]);
                assert(inc_w[inc_w.len() - 1] == p);
                assert(mountain[k + 1] == dec_tail[0]);
                assert(dec_tail[0] == dec_w[1]);
                assert(dec_w[0] == p);
                assert(nums[dec_w[0]] > nums[dec_w[1]]);
            } else {
                let dk = k - inc_w.len() as int;
                assert(mountain[k] == dec_tail[dk]);
                assert(mountain[k + 1] == dec_tail[dk + 1]);
                assert(dec_tail[dk] == dec_w[dk + 1]);
                assert(dec_tail[dk + 1] == dec_w[dk + 2]);
                assert(nums[dec_w[dk + 1]] > nums[dec_w[dk + 2]]);
            }
        }
        assert forall |k: int| peak_pos <= k < mountain.len() - 1 implies
            (#[trigger] nums[mountain[k]]) > nums[mountain[k + 1]] by {
            if k == peak_pos {
                assert(mountain[k] == inc_w[inc_w.len() - 1]);
                assert(inc_w[inc_w.len() - 1] == p);
                assert(mountain[k + 1] == dec_tail[0]);
                assert(dec_tail[0] == dec_w[1]);
                assert(dec_w[0] == p);
            } else {
                let dk = k - inc_w.len() as int;
                assert(mountain[k] == dec_tail[dk]);
                assert(mountain[k + 1] == dec_tail[dk + 1]);
                assert(dec_tail[dk] == dec_w[dk + 1]);
                assert(dec_tail[dk + 1] == dec_w[dk + 2]);
            }
        }
        assert forall |k: int| peak_pos <= k < mountain.len() - 1 implies
            mountain[k] < mountain[k + 1]
            && (#[trigger] nums[mountain[k]]) > nums[mountain[k + 1]] by {
            assert(mountain[k] < mountain[k + 1]);
            assert(nums[mountain[k]] > nums[mountain[k + 1]]);
        }

        assert(Self::is_mountain_subseq(nums, mountain, peak_pos));
    }

    proof fn lemma_mountain_optimal(nums: Seq<i32>, indices: Seq<int>, peak: int)
        requires Self::is_mountain_subseq(nums, indices, peak),
        ensures indices.len() <= Self::max_mountain_len(nums, nums.len() as int - 1),
    {
        let peak_arr_idx = indices[peak];
        let asc = indices.subrange(0, peak + 1);
        let desc = indices.subrange(peak, indices.len() as int);

        
        assert(asc[asc.len() - 1] == peak_arr_idx);
        assert forall |k: int| 0 <= k < asc.len() implies
            0 <= (#[trigger] asc[k]) < nums.len() by { assert(asc[k] == indices[k]); }
        assert forall |k: int| 0 <= k < asc.len() - 1 implies
            (#[trigger] asc[k]) < asc[k + 1] by {
            assert(asc[k] == indices[k]);
            assert(asc[k + 1] == indices[k + 1]);
            assert(nums[indices[k]] < nums[indices[k + 1]]);
        }
        assert forall |k: int| 0 <= k < asc.len() - 1 implies
            (#[trigger] nums[asc[k]]) < nums[asc[k + 1]] by {
            assert(asc[k] == indices[k]);
            assert(asc[k + 1] == indices[k + 1]);
        }
        assert forall |k: int| 0 <= k < asc.len() - 1 implies
            asc[k] < asc[k + 1]
            && (#[trigger] nums[asc[k]]) < nums[asc[k + 1]] by {
            assert(asc[k] < asc[k + 1]);
            assert(nums[asc[k]] < nums[asc[k + 1]]);
        }
        assert(is_inc_subseq_ending_at(nums, asc, peak_arr_idx));
        Self::lemma_lis_optimal(nums, peak_arr_idx, asc);

        
        assert(desc[0] == peak_arr_idx);
        assert forall |k: int| 0 <= k < desc.len() implies
            0 <= (#[trigger] desc[k]) < nums.len() by { assert(desc[k] == indices[k + peak]); }
        assert forall |k: int| 0 <= k < desc.len() - 1 implies
            (#[trigger] desc[k]) < desc[k + 1] by {
            assert(desc[k] == indices[k + peak]);
            assert(desc[k + 1] == indices[k + peak + 1]);
            assert(nums[indices[k + peak]] > nums[indices[k + peak + 1]]);
        }
        assert forall |k: int| 0 <= k < desc.len() - 1 implies
            (#[trigger] nums[desc[k]]) > nums[desc[k + 1]] by {
            assert(desc[k] == indices[k + peak]);
            assert(desc[k + 1] == indices[k + peak + 1]);
        }
        assert forall |k: int| 0 <= k < desc.len() - 1 implies
            desc[k] < desc[k + 1]
            && (#[trigger] nums[desc[k]]) > nums[desc[k + 1]] by {
            assert(desc[k] < desc[k + 1]);
            assert(nums[desc[k]] > nums[desc[k + 1]]);
        }
        assert(is_dec_subseq_starting_at(nums, desc, peak_arr_idx));
        Self::lemma_lds_optimal(nums, peak_arr_idx, desc);

        assert(indices.len() == asc.len() + desc.len() - 1);
        Self::lemma_max_mountain_len_includes(nums, nums.len() as int - 1, peak_arr_idx);
    }

    proof fn lemma_precondition_implies_mountain_exists(nums: Seq<i32>, a: int, b: int, c: int)
        requires
            0 <= a < b < c < nums.len(),
            nums[a] < nums[b],
            nums[b] > nums[c],
        ensures Self::max_mountain_len(nums, nums.len() as int - 1) >= 3,
    {
        Self::lemma_lis_at_pos(nums, a);
        Self::lemma_lis_at_pos(nums, b);
        Self::lemma_lds_at_pos(nums, b);
        Self::lemma_lds_at_pos(nums, c);
        Self::lemma_lis_max_scan_includes(nums, b, b, a);
        
        
        reveal_with_fuel(Solution::lis_at, 2);
        assert(Self::lis_at(nums, b) >= 2);
        Self::lemma_lds_max_scan_includes(nums, b, nums.len() as int - 1, c);
        
        
        reveal_with_fuel(Solution::lds_at, 2);
        assert(Self::lds_at(nums, b) >= 2);
        assert(Self::mountain_len_at(nums, b) >= 3);
        Self::lemma_max_mountain_len_includes(nums, nums.len() as int - 1, b);
    }

    pub fn minimum_mountain_removals(nums: Vec<i32>) -> (result: i32)
        requires
            3 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000i32,
            exists |a: int, b: int, c: int| 0 <= a < b < c < nums.len() as int
                && nums[a] < nums[b] && nums[b] > nums[c],
        ensures
            result >= 0,
            exists |indices: Seq<int>, peak: int| Self::is_mountain_subseq(nums@, indices, peak)
                && indices.len() == nums.len() - result as int,
            forall |indices: Seq<int>, peak: int| Self::is_mountain_subseq(nums@, indices, peak)
                ==> indices.len() <= nums.len() - result as int,
    {
        let n = nums.len();

        let mut lis: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                0 <= idx <= n,
                lis.len() == idx,
                forall |k: int| 0 <= k < idx as int ==> lis[k] == 1i32,
            decreases n - idx,
        {
            lis.push(1i32);
            idx = idx + 1;
        }

        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                lis.len() == n,
                n == nums.len(),
                3 <= n <= 1000,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1_000_000_000i32,
                forall |k: int| 0 <= k < i as int ==> lis[k] as int == Self::lis_at(nums@, k),
                forall |k: int| i as int <= k < n as int ==> lis[k] == 1i32,
                forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] lis[k] as int <= k + 1,
            decreases n - i,
        {
            let mut j: usize = 0;
            while j < i
                invariant
                    0 <= j <= i,
                    1 <= i < n,
                    lis.len() == n,
                    n == nums.len(),
                    3 <= n <= 1000,
                    forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1_000_000_000i32,
                    forall |k: int| 0 <= k < i as int ==> lis[k] as int == Self::lis_at(nums@, k),
                    forall |k: int| i as int + 1 <= k && k < n as int ==> lis[k] == 1i32,
                    forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] lis[k] as int <= k + 1,
                    lis[i as int] as int - 1 == Self::lis_max_scan(nums@, i as int, j as int),
                    1 <= lis[i as int] as int <= i as int + 1,
                decreases i - j,
            {
                if nums[j] < nums[i] {
                    if lis[j] + 1 > lis[i] {
                        lis.set(i, lis[j] + 1);
                    }
                }
                proof {
                    reveal_with_fuel(Solution::lis_max_scan, 2);
                }
                j = j + 1;
            }
            proof {
                reveal_with_fuel(Solution::lis_at, 2);
            }
            i = i + 1;
        }

        let mut lds: Vec<i32> = Vec::new();
        idx = 0;
        while idx < n
            invariant
                0 <= idx <= n,
                lds.len() == idx,
                forall |k: int| 0 <= k < idx as int ==> lds[k] == 1i32,
            decreases n - idx,
        {
            lds.push(1i32);
            idx = idx + 1;
        }

        let mut k: usize = 1;
        while k < n
            invariant
                1 <= k <= n,
                lds.len() == n,
                lis.len() == n,
                n == nums.len(),
                3 <= n <= 1000,
                forall |m: int| 0 <= m < nums.len() ==> 1 <= #[trigger] nums[m] <= 1_000_000_000i32,
                forall |m: int| (n - k) as int <= m < n as int ==> lds[m] as int == Self::lds_at(nums@, m),
                forall |m: int| 0 <= m < (n - k) as int ==> lds[m] == 1i32,
                forall |m: int| (n - k) as int <= m < n as int ==> 1 <= #[trigger] lds[m] as int <= n as int - m,
                forall |m: int| 0 <= m < n as int ==> lis[m] as int == Self::lis_at(nums@, m),
                forall |m: int| 0 <= m < n as int ==> 1 <= #[trigger] lis[m] as int <= m + 1,
            decreases n - k,
        {
            let i_idx: usize = n - 1 - k;
            let mut j: usize = i_idx + 1;
            while j < n
                invariant
                    i_idx + 1 <= j <= n,
                    i_idx == n - 1 - k,
                    i_idx < n - 1,
                    1 <= k < n,
                    lds.len() == n,
                    n == nums.len(),
                    3 <= n <= 1000,
                    forall |m: int| 0 <= m < nums.len() ==> 1 <= #[trigger] nums[m] <= 1_000_000_000i32,
                    forall |m: int| i_idx as int + 1 <= m && m < n as int ==> lds[m] as int == Self::lds_at(nums@, m),
                    forall |m: int| 0 <= m < i_idx as int ==> lds[m] == 1i32,
                    forall |m: int| i_idx as int + 1 <= m && m < n as int ==> 1 <= #[trigger] lds[m] as int <= n as int - m,
                    lds[i_idx as int] as int - 1 == Self::lds_max_scan(nums@, i_idx as int, (j - 1) as int),
                    1 <= lds[i_idx as int] as int <= n as int - i_idx as int,
                decreases n - j,
            {
                if nums[j] < nums[i_idx] {
                    if lds[j] + 1 > lds[i_idx] {
                        lds.set(i_idx, lds[j] + 1);
                    }
                }
                proof {
                    reveal_with_fuel(Solution::lds_max_scan, 2);
                }
                j = j + 1;
            }
            proof {
                reveal_with_fuel(Solution::lds_at, 2);
            }
            k = k + 1;
        }

        let mut result: i32 = n as i32;
        let mut i2: usize = 0;
        while i2 < n
            invariant
                0 <= i2 <= n,
                lis.len() == n,
                lds.len() == n,
                n == nums.len(),
                3 <= n <= 1000,
                forall |m: int| 0 <= m < n as int ==> lis[m] as int == Self::lis_at(nums@, m),
                forall |m: int| 0 <= m < n as int ==> lds[m] as int == Self::lds_at(nums@, m),
                forall |m: int| 0 <= m < n as int ==> 1 <= #[trigger] lis[m] as int <= m + 1,
                forall |m: int| 0 <= m < n as int ==> 1 <= #[trigger] lds[m] as int <= n as int - m,
                result as int == n as int - Self::max_mountain_len(nums@, i2 as int - 1),
                0 <= result <= n as i32,
            decreases n - i2,
        {
            if lis[i2] > 1 && lds[i2] > 1 {
                let mountain_len: i32 = lis[i2] + lds[i2] - 1;
                let removals: i32 = n as i32 - mountain_len;
                if removals < result {
                    result = removals;
                }
            }
            proof {
                reveal_with_fuel(Solution::max_mountain_len, 2);
                Self::lemma_max_mountain_len_nonneg(nums@, i2 as int - 1);
            }
            i2 = i2 + 1;
        }

        
        proof {
            assert(result as int == n as int - Self::max_mountain_len(nums@, n as int - 1));

            
            let (a, b, c): (int, int, int) = choose |a: int, b: int, c: int|
                0 <= a < b < c < nums.len() as int
                && nums@[a] < nums@[b] && nums@[b] > nums@[c];
            Self::lemma_precondition_implies_mountain_exists(nums@, a, b, c);

            
            Self::lemma_max_mountain_len_nonneg(nums@, n as int - 1);

            
            Self::lemma_mountain_achievable(nums@, n as int);

            
            assert forall |indices: Seq<int>, peak: int|
                Self::is_mountain_subseq(nums@, indices, peak)
                implies indices.len() <= nums.len() - result as int by {
                Self::lemma_mountain_optimal(nums@, indices, peak);
            }
        }

        result
    }
}

}
