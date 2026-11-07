use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn popcount_steps(t: nat, rem: nat) -> nat
        decreases rem,
    {
        if rem == 0 {
            0
        } else {
            (t % 2) + Self::popcount_steps(t / 2, (rem - 1) as nat)
        }
    }

    pub open spec fn sum_selected_prefix(nums: Seq<i32>, k: int, upto: nat) -> int
        recommends
            upto <= nums.len(),
        decreases upto,
    {
        if upto == 0 {
            0
        } else {
            Self::sum_selected_prefix(nums, k, (upto - 1) as nat)
                + if Self::popcount_steps((upto - 1) as nat, 10) as int == k {
                    nums[upto - 1] as int
                } else {
                    0
                }
        }
    }

    pub fn sum_indices_with_k_set_bits(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 1000,
            0 <= k <= 10,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums@[i],
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums@[i] <= 100000,
        ensures
            result as int == (Self::sum_selected_prefix(nums@, k as int, nums.len() as nat) as i32) as int,
    {
        let mut res: i128 = 0;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                i <= nums.len(),
                nums.len() <= 1000,
                -2147483648 * i as int <= res as int <= 2147483647 * i as int,
                res as int == Self::sum_selected_prefix(nums@, k as int, i as nat),
            decreases nums.len() - i,
        {
            let mut t: usize = i;
            let mut b: usize = 0;
            let mut cnt: i32 = 0;
            while b < 10
                invariant
                    b <= 10,
                    0 <= cnt <= b as int,
                    t as int >= 0,
                    cnt as int + Self::popcount_steps(t as nat, (10 - b) as nat) as int == Self::popcount_steps(i as nat, 10) as int,
                decreases 10 - b,
            {
                if t % 2 == 1 {
                    assert(t as int % 2 == 1);
                    cnt = cnt + 1;
                    assert((cnt - 1) as int + Self::popcount_steps(t as nat, (10 - b) as nat) as int == Self::popcount_steps(i as nat, 10) as int);
                    assert(Self::popcount_steps(t as nat, (10 - b) as nat) == (t as nat % 2) + Self::popcount_steps((t / 2) as nat, (10 - (b + 1)) as nat));
                    assert(cnt as int + Self::popcount_steps((t / 2) as nat, (10 - (b + 1)) as nat) as int == Self::popcount_steps(i as nat, 10) as int);
                } else {
                    assert(t as int % 2 == 0);
                    assert(Self::popcount_steps(t as nat, (10 - b) as nat) == (t as nat % 2) + Self::popcount_steps((t / 2) as nat, (10 - (b + 1)) as nat));
                    assert(cnt as int + Self::popcount_steps((t / 2) as nat, (10 - (b + 1)) as nat) as int == Self::popcount_steps(i as nat, 10) as int);
                }
                t = t / 2;
                b = b + 1;
            }
            assert(b == 10);
            assert(Self::popcount_steps(t as nat, (10 - b) as nat) == 0);
            assert(cnt as int == Self::popcount_steps(i as nat, 10) as int);
            let add: i128 = if cnt == k { nums[i] as i128 } else { 0 };
            if cnt == k {
                assert(Self::popcount_steps(i as nat, 10) as int == k as int);
                assert(add as int == nums[i as int] as int);
            } else {
                assert(Self::popcount_steps(i as nat, 10) as int != k as int);
                assert(add as int == 0);
            }
            assert(-2147483648 <= add as int <= 2147483647);
            res = res + add;
            assert(res as int == Self::sum_selected_prefix(nums@, k as int, (i + 1) as nat));
            assert(-2147483648 * (i + 1) as int <= res as int <= 2147483647 * (i + 1) as int);
            i = i + 1;
        }
        assert(i == nums.len());
        assert((res as i32) as int == (Self::sum_selected_prefix(nums@, k as int, nums.len() as nat) as i32) as int);
        res as i32
    }
}

}
