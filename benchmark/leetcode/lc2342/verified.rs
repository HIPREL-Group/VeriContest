use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_sum_spec(x: nat) -> nat
        decreases x,
    {
        if x == 0 {
            0
        } else {
            (x % 10) + Self::digit_sum_spec(x / 10)
        }
    }

    pub open spec fn valid_pair(nums: Seq<i32>, i: int, j: int) -> bool {
        0 <= i < j < nums.len()
            && Self::digit_sum_spec(nums[i] as nat) == Self::digit_sum_spec(nums[j] as nat)
    }

    fn digit_sum(mut x: i32) -> (result: i64)
        requires
            x >= 0,
            x <= 1000000000,
        ensures
            0 <= result,
            result as nat == Self::digit_sum_spec(x as nat),
    {
        let orig: i64 = x as i64;
        let mut s: i64 = 0;
        while x > 0
            invariant
                0 <= x,
                0 <= s,
                s <= 9 * ((orig - x as i64) + 1),
                0 <= orig <= 1000000000,
                s as nat + Self::digit_sum_spec(x as nat) == Self::digit_sum_spec(orig as nat),
            decreases x,
        {
            let old_x = x;
            proof {
                assert(0 <= x % 10 <= 9);
                assert(x / 10 <= x - 1);
                assert(orig - (x / 10) as i64 >= (orig - x as i64) + 1);
                assert(old_x > 0);
                assert(Self::digit_sum_spec(old_x as nat)
                    == (old_x % 10) as nat + Self::digit_sum_spec((old_x / 10) as nat));
                assert(s + (x % 10) as i64 <= 9 * ((orig - (x / 10) as i64) + 1)) by (nonlinear_arith)
                    requires
                        s <= 9 * ((orig - x as i64) + 1),
                        0 <= x % 10 <= 9,
                        orig - (x / 10) as i64 >= (orig - x as i64) + 1,
                ;
                assert(s + (x % 10) as i64 <= 9223372036854775807);
                assert(s as nat + (old_x % 10) as nat + Self::digit_sum_spec((old_x / 10) as nat)
                    == Self::digit_sum_spec(orig as nat));
            }
            s = s + (x % 10) as i64;
            x = x / 10;
        }
        proof {
            assert(x == 0);
            assert(Self::digit_sum_spec(0) == 0);
            assert(s as nat == Self::digit_sum_spec(orig as nat));
        }
        s
    }

    pub fn maximum_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
        ensures
            -1 <= result as int <= 2000000000,
            result == -1 ==> forall |i: int, j: int|
                0 <= i < j < nums.len() ==> !(#[trigger] Self::valid_pair(nums@, i, j)),
            result != -1 ==> exists |i: int, j: int|
                0 <= i < j < nums.len()
                && Self::valid_pair(nums@, i, j)
                && result as int == nums[i] as int + nums[j] as int,
            result != -1 ==> forall |i: int, j: int|
                0 <= i < j < nums.len() && #[trigger] Self::valid_pair(nums@, i, j)
                ==> nums[i] as int + nums[j] as int <= result as int,
    {
        let mut ans: i32 = -1;
        let n = nums.len();
        let mut i: usize = 0;
        let mut found: bool = false;
        let mut bi: usize = 0;
        let mut bj: usize = 0;

        while i < n
            invariant
                i <= n,
                n == nums.len(),
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000000000,
                -1 <= ans as int <= 2000000000,
                (!found) ==> ans == -1,
                found ==> 0 <= bi < bj < n,
                found ==> bi < i,
                found ==> Self::valid_pair(nums@, bi as int, bj as int),
                found ==> ans as int == nums@[bi as int] as int + nums@[bj as int] as int,
                forall |a: int, b: int|
                    0 <= a < b < n && a < i && Self::valid_pair(nums@, a, b)
                    ==> found && nums[a] as int + nums[b] as int <= ans as int,
            decreases n - i,
        {
            let mut j: usize = i + 1;
            while j < n
                invariant
                    i < n,
                    i + 1 <= j <= n,
                    n == nums.len(),
                    forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000000000,
                    -1 <= ans as int <= 2000000000,
                    (!found) ==> ans == -1,
                    found ==> 0 <= bi < bj < n,
                    found ==> (bi < i || (bi == i && bj < j)),
                    found ==> Self::valid_pair(nums@, bi as int, bj as int),
                    found ==> ans as int == nums@[bi as int] as int + nums@[bj as int] as int,
                    forall |a: int, b: int|
                        0 <= a < b < n
                        && (a < i || (a == i && b < j))
                        && Self::valid_pair(nums@, a, b)
                        ==> found && nums[a] as int + nums[b] as int <= ans as int,
                decreases n - j,
            {
                let si = Self::digit_sum(nums[i]);
                let sj = Self::digit_sum(nums[j]);
                if si == sj {
                    proof {
                        assert(si as nat == Self::digit_sum_spec(nums@[i as int] as nat));
                        assert(sj as nat == Self::digit_sum_spec(nums@[j as int] as nat));
                        assert(Self::valid_pair(nums@, i as int, j as int));
                        assert(nums@[i as int] as int + nums@[j as int] as int <= 2000000000);
                    }
                    let cur = nums[i] + nums[j];
                    if !found || cur > ans {
                        found = true;
                        bi = i;
                        bj = j;
                        ans = cur;
                    } else {
                        proof {
                            assert(cur as int <= ans as int);
                        }
                    }
                }
                j = j + 1;
            }
            i = i + 1;
        }

        proof {
            if !found {
                assert(ans == -1);
                assert(forall |a: int, b: int|
                    0 <= a < b < n ==> !Self::valid_pair(nums@, a, b));
            } else {
                assert(0 <= bi < bj < n);
                assert(Self::valid_pair(nums@, bi as int, bj as int));
                assert(ans as int == nums@[bi as int] as int + nums@[bj as int] as int);
                assert(forall |a: int, b: int|
                    0 <= a < b < n && Self::valid_pair(nums@, a, b)
                    ==> nums[a] as int + nums[b] as int <= ans as int);
            }
        }

        ans
    }
}

}
