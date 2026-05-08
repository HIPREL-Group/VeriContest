use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_occurrences(s: Seq<i32>, value: i32) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            Self::count_occurrences(s.drop_last(), value)
                + if s.last() == value { 1 as nat } else { 0 as nat }
        }
    }

    proof fn count_extend(s: Seq<i32>, i: int, v: i32)
        requires 0 <= i < s.len()
        ensures Self::count_occurrences(s.subrange(0, i + 1), v) ==
                Self::count_occurrences(s.subrange(0, i), v) +
                (if s[i] == v { 1 as nat } else { 0 as nat })
    {
        let sub = s.subrange(0, i + 1);
        assert(sub.drop_last() =~= s.subrange(0, i));
        assert(sub.last() == s[i]);
    }

    proof fn count_implies_index(s: Seq<i32>, v: i32)
        requires Self::count_occurrences(s, v) >= 1
        ensures exists |i: int| 0 <= i < s.len() && s[i] == v
        decreases s.len()
    {
        if s.last() == v {
            assert(s[s.len() - 1] == v);
        } else {
            Self::count_implies_index(s.drop_last(), v);
            let i = choose |i: int| 0 <= i < s.drop_last().len() && s.drop_last()[i] == v;
            assert(s[i] == v);
        }
    }

    fn count_in_vec(nums: &Vec<i32>, value: i32) -> (count: usize)
        requires nums.len() <= 30_000
        ensures count as nat == Self::count_occurrences(nums@, value)
    {
        let mut count: usize = 0;
        let mut j: usize = 0;
        while j < nums.len()
            invariant
                0 <= j <= nums.len(),
                count as nat == Self::count_occurrences(nums@.subrange(0, j as int), value),
                count <= j,
            decreases nums.len() - j,
        {
            proof { Self::count_extend(nums@, j as int, value); }
            if nums[j] == value { count = count + 1; }
            j = j + 1;
        }
        proof { assert(nums@.subrange(0, nums@.len() as int) =~= nums@); }
        count
    }

    fn find_unique_pair(nums: &Vec<i32>) -> (result: Vec<i32>)
        requires
            nums.len() <= 30_000,
            exists |a: i32, b: i32| {
                a != b
                && Self::count_occurrences(nums@, a) == 1
                && Self::count_occurrences(nums@, b) == 1
                && forall |x: i32| x != a && x != b ==> Self::count_occurrences(nums@, x) == 0 || #[trigger] Self::count_occurrences(nums@, x) == 2
            },
        ensures
            result.len() == 2,
            Self::count_occurrences(nums@, result[0]) == 1,
            Self::count_occurrences(nums@, result[1]) == 1,
    {
        let ghost a_spec: i32 = choose |a: i32| exists |b: i32| (
            a != b
            && #[trigger] Self::count_occurrences(nums@, a) == 1
            && Self::count_occurrences(nums@, b) == 1
            && forall |x: i32| x != a && x != b ==> Self::count_occurrences(nums@, x) == 0 || #[trigger] Self::count_occurrences(nums@, x) == 2
        );
        let ghost b_spec: i32 = choose |b: i32| (
            a_spec != b
            && Self::count_occurrences(nums@, a_spec) == 1
            && #[trigger] Self::count_occurrences(nums@, b) == 1
            && forall |x: i32| x != a_spec && x != b ==> Self::count_occurrences(nums@, x) == 0 || #[trigger] Self::count_occurrences(nums@, x) == 2
        );

        let mut i: usize = 0;
        let mut first: i32 = 0;
        let mut found_first: bool = false;

        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() <= 30_000,
                found_first ==> Self::count_occurrences(nums@, first) == 1,
                !found_first ==> forall |k: int| 0 <= k < i ==> Self::count_occurrences(nums@, nums@[k]) != 1,
            decreases nums.len() - i,
        {
            if !found_first {
                let c = Self::count_in_vec(nums, nums[i]);
                if c == 1 {
                    first = nums[i];
                    found_first = true;
                }
            }
            i = i + 1;
        }

        proof {
            if !found_first {
                Self::count_implies_index(nums@, a_spec);
                let ia: int = choose |ia: int| 0 <= ia < nums@.len() && nums@[ia] == a_spec;
                assert(Self::count_occurrences(nums@, nums@[ia]) == 1);
                assert(false);
            }
        }

        let mut k: usize = 0;
        let mut second: i32 = 0;
        let mut found_second: bool = false;

        while k < nums.len()
            invariant
                0 <= k <= nums.len(),
                nums.len() <= 30_000,
                Self::count_occurrences(nums@, first) == 1,
                found_second ==> (Self::count_occurrences(nums@, second) == 1 && second != first),
                !found_second ==> forall |m: int| 0 <= m < k ==> (nums@[m] == first || Self::count_occurrences(nums@, nums@[m]) != 1),
            decreases nums.len() - k,
        {
            if !found_second {
                if nums[k] != first {
                    let c = Self::count_in_vec(nums, nums[k]);
                    if c == 1 {
                        second = nums[k];
                        found_second = true;
                    }
                }
            }
            k = k + 1;
        }

        proof {
            if !found_second {
                assert(first == a_spec || first == b_spec) by {
                    if first != a_spec && first != b_spec {
                        assert(Self::count_occurrences(nums@, first) == 0 || Self::count_occurrences(nums@, first) == 2);
                    }
                };
                let other: i32 = if first == a_spec { b_spec } else { a_spec };
                assert(Self::count_occurrences(nums@, other) == 1);
                assert(other != first);
                Self::count_implies_index(nums@, other);
                let idx: int = choose |idx: int| 0 <= idx < nums@.len() && nums@[idx] == other;
                assert(nums@[idx] != first);
                assert(Self::count_occurrences(nums@, nums@[idx]) == 1);
                assert(false);
            }
        }

        let mut result: Vec<i32> = Vec::new();
        result.push(first);
        result.push(second);
        result
    }

    pub fn single_number(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 30_000,
            forall |i: int| 0 <= i < nums.len() ==> -2_147_483_648 <= #[trigger] nums[i] <= 2_147_483_647,
            exists |a: i32, b: i32| {
                a != b
                && Self::count_occurrences(nums@, a) == 1
                && Self::count_occurrences(nums@, b) == 1
                && forall |x: i32| x != a && x != b ==> Self::count_occurrences(nums@, x) == 0 || Self::count_occurrences(nums@, x) == 2
            },
        ensures
            result.len() == 2,
            Self::count_occurrences(nums@, result[0]) == 1,
            Self::count_occurrences(nums@, result[1]) == 1,
    {
        let mut xor_all: i32 = 0;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
            decreases nums.len() - i,
        {
            xor_all = xor_all ^ nums[i];
            i = i + 1;
        }

        let mut mask: i32 = 1;
        let mut shift: u32 = 0;
        while shift < 31 && (xor_all & mask) == 0
            invariant
                0 <= shift <= 31,
            decreases 31 - shift,
        {
            mask = mask << 1;
            shift = shift + 1;
        }

        let mut a: i32 = 0;
        let mut b: i32 = 0;
        let mut j: usize = 0;
        while j < nums.len()
            invariant
                0 <= j <= nums.len(),
            decreases nums.len() - j,
        {
            if (nums[j] & mask) == 0 {
                a = a ^ nums[j];
            } else {
                b = b ^ nums[j];
            }
            j = j + 1;
        }

        let count_a = Self::count_in_vec(&nums, a);
        let count_b = Self::count_in_vec(&nums, b);

        if count_a == 1 && count_b == 1 {
            let mut result: Vec<i32> = Vec::new();
            result.push(a);
            result.push(b);
            result
        } else {
            Self::find_unique_pair(&nums)
        }
    }
}

}
