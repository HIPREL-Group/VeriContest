use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sorted(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn count_occ(s: Seq<i32>, val: i32) -> int
        decreases s.len(),
    {
        if s.len() == 0 { 0 }
        else {
            (if s.last() == val { 1int } else { 0int })
                + Self::count_occ(s.drop_last(), val)
        }
    }

    pub open spec fn is_perm(a: Seq<i32>, b: Seq<i32>) -> bool {
        a.len() == b.len() && forall|v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    pub open spec fn even_index_sum(s: Seq<i32>) -> int
        decreases s.len(),
    {
        if s.len() < 1 {
            0int
        } else if s.len() < 2 {
            s[0] as int
        } else {
            s[0] as int + Self::even_index_sum(s.subrange(2, s.len() as int))
        }
    }

    fn ms_merge(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>) {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < a.len() || j < b.len()
        {
            if i < a.len() && (j >= b.len() || a[i] <= b[j]) {
                result.push(a[i]);
                i = i + 1;
            } else {
                result.push(b[j]);
                j = j + 1;
            }
        }
        result
    }

    fn ms_sort(nums: &Vec<i32>) -> (result: Vec<i32>) {
        let n = nums.len();
        if n <= 1 {
            let mut result = Vec::new();
            if n == 1 {
                result.push(nums[0]);
            }
            return result;
        }
        let mid = n / 2;
        let mut left: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < mid
        {
            left.push(nums[i]);
            i = i + 1;
        }
        let mut right: Vec<i32> = Vec::new();
        let mut j: usize = mid;
        while j < n
        {
            right.push(nums[j]);
            j = j + 1;
        }
        let sorted_left = Self::ms_sort(&left);
        let sorted_right = Self::ms_sort(&right);
        let result = Self::ms_merge(&sorted_left, &sorted_right);
        result
    }

    pub fn max_coins(piles: Vec<i32>) -> (result: i32)
        requires
            3 <= piles.len() <= 100000,
            piles.len() % 3 == 0,
            forall|i: int| 0 <= i < piles.len() ==> 1 <= #[trigger] piles[i] <= 10000,
        ensures
            exists|sorted_piles: Seq<i32>|
                Self::sorted(sorted_piles)
                && sorted_piles.len() == piles.len()
                && result as int == Self::even_index_sum(
                    sorted_piles.subrange(
                        (sorted_piles.len() / 3) as int,
                        sorted_piles.len() as int,
                    ),
                ),
    {
        let sorted = Self::ms_sort(&piles);
        let n = sorted.len();

        let mut sum: i32 = 0;
        let third = n / 3;
        let mut k = third;
        while k < n {
            sum = sum + sorted[k];
            k = k + 2;
        }

        sum
    }
}

}
