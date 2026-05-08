use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_value(nums: Seq<i32>, value: int, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_value(nums, value, end - 1)
                + if nums[end - 1] as int == value { 1int } else { 0int }
        }
    }

    pub open spec fn repeat_value(value: int, times: int) -> Seq<i32>
        decreases times,
    {
        if times <= 0 {
            seq![]
        } else {
            Self::repeat_value(value, times - 1).push(value as i32)
        }
    }

    pub open spec fn sorted_values(nums: Seq<i32>, upto: int) -> Seq<i32>
        decreases upto,
    {
        if upto <= 0 {
            seq![]
        } else {
            Self::sorted_values(nums, upto - 1)
                + Self::repeat_value(upto, Self::count_value(nums, upto, nums.len() as int))
        }
    }

    pub open spec fn swapped_pairs(sorted: Seq<i32>, pairs: int) -> Seq<i32>
        decreases pairs,
    {
        if pairs <= 0 {
            seq![]
        } else {
            let prev = Self::swapped_pairs(sorted, pairs - 1);
            let i = 2 * (pairs - 1);
            prev + seq![sorted[i + 1], sorted[i]]
        }
    }

    proof fn lemma_swapped_pairs_push_ignored(s: Seq<i32>, x: i32, pairs: int)
        requires
            0 <= pairs,
            2 * pairs <= s.len(),
        ensures
            Self::swapped_pairs(s.push(x), pairs) == Self::swapped_pairs(s, pairs),
        decreases pairs,
    {
        if pairs <= 0 {
        } else {
            Self::lemma_swapped_pairs_push_ignored(s, x, pairs - 1);
            reveal_with_fuel(Solution::swapped_pairs, 2);
            assert(s.push(x)[2 * (pairs - 1) + 1] == s[2 * (pairs - 1) + 1]);
            assert(s.push(x)[2 * (pairs - 1)] == s[2 * (pairs - 1)]);
        }
    }

    fn count_value_exec(nums: &Vec<i32>, value: i32) -> (c: i32)
        requires
            nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            c as int == Self::count_value(nums@, value as int, nums.len() as int),
            0 <= c <= nums.len(),
    {
        let n = nums.len();
        let mut i: usize = 0;
        let mut c: i32 = 0;
        while i < n
            invariant
                n == nums.len(),
                n <= 100,
                0 <= i <= n,
                c as int == Self::count_value(nums@, value as int, i as int),
                0 <= c <= i,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
            decreases n - i,
        {
            if nums[i] == value {
                c = c + 1;
            }
            i = i + 1;
        }
        c
    }

    pub fn number_game(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 100,
            nums.len() % 2 == 0,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result@ == Self::swapped_pairs(Self::sorted_values(nums@, 100), (Self::sorted_values(nums@, 100).len() / 2) as int),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut has_pending = false;
        let mut pending: i32 = 0;
        let mut value: i32 = 1;
        while value <= 100
            invariant
                1 <= value <= 101,
                nums.len() <= 100,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                result@ == Self::swapped_pairs(Self::sorted_values(nums@, value as int - 1), (Self::sorted_values(nums@, value as int - 1).len() / 2) as int),
                has_pending == (Self::sorted_values(nums@, value as int - 1).len() % 2 == 1),
                has_pending ==> pending == Self::sorted_values(nums@, value as int - 1)[Self::sorted_values(nums@, value as int - 1).len() - 1],
            decreases 101 - value,
        {
            let cnt = Self::count_value_exec(&nums, value);
            let mut t: i32 = 0;
            while t < cnt
                invariant
                    0 <= t <= cnt,
                    result@ == Self::swapped_pairs(
                        Self::sorted_values(nums@, value as int - 1) + Self::repeat_value(value as int, t as int),
                        ((Self::sorted_values(nums@, value as int - 1) + Self::repeat_value(value as int, t as int)).len() / 2) as int,
                    ),
                    has_pending == ((Self::sorted_values(nums@, value as int - 1) + Self::repeat_value(value as int, t as int)).len() % 2 == 1),
                    has_pending ==> pending == (Self::sorted_values(nums@, value as int - 1) + Self::repeat_value(value as int, t as int))[
                        (Self::sorted_values(nums@, value as int - 1) + Self::repeat_value(value as int, t as int)).len() - 1
                    ],
                decreases cnt - t,
            {
                let ghost base = Self::sorted_values(nums@, value as int - 1);
                let ghost pref = base + Self::repeat_value(value as int, t as int);
                let old_has_pending = has_pending;
                let old_pending = pending;
                let ghost old_result = result@;
                if has_pending {
                    result.push(value);
                    result.push(pending);
                    has_pending = false;
                } else {
                    pending = value;
                    has_pending = true;
                }
                proof {
                    let ghost next_pref = base + Self::repeat_value(value as int, (t + 1) as int);
                    assert(next_pref == pref.push(value));
                    if old_has_pending {
                        assert(old_result == Self::swapped_pairs(pref, (pref.len() / 2) as int));
                        assert(old_pending == pref[pref.len() - 1]);
                        assert(result@ == old_result + seq![value, old_pending]);
                        Self::lemma_swapped_pairs_push_ignored(pref, value, (pref.len() / 2) as int);
                        reveal_with_fuel(Solution::swapped_pairs, 2);
                        assert(next_pref[2 * ((pref.len() / 2) as int) + 1] == value);
                        assert(next_pref[2 * ((pref.len() / 2) as int)] == old_pending);
                        assert(Self::swapped_pairs(next_pref, (next_pref.len() / 2) as int)
                            == Self::swapped_pairs(pref, (pref.len() / 2) as int) + seq![value, old_pending]);
                    } else {
                        assert(old_result == Self::swapped_pairs(pref, (pref.len() / 2) as int));
                        assert(result@ == old_result);
                        Self::lemma_swapped_pairs_push_ignored(pref, value, (pref.len() / 2) as int);
                        assert(Self::swapped_pairs(next_pref, (next_pref.len() / 2) as int)
                            == Self::swapped_pairs(pref, (pref.len() / 2) as int));
                    }
                }
                t = t + 1;
            }
            value = value + 1;
        }
        result
    }
}

}
