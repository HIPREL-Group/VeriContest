use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn concat_num_spec(left: int, right: int) -> int {
        if right < 10 {
            left * 10 + right
        } else if right < 100 {
            left * 100 + right
        } else if right < 1000 {
            left * 1000 + right
        } else if right < 10000 {
            left * 10000 + right
        } else {
            left * 100000 + right
        }
    }

    pub open spec fn conc_val_taken(nums: Seq<i32>, taken: nat) -> int
        recommends taken as int <= nums.len() / 2,
        decreases taken,
    {
        if taken == 0 {
            0
        } else {
            Self::conc_val_taken(nums, (taken - 1) as nat)
                + Self::concat_num_spec(
                    nums[(taken - 1) as int] as int,
                    nums[nums.len() - taken as int] as int,
                )
        }
    }

    pub open spec fn conc_val_spec(nums: Seq<i32>) -> int {
        let taken = (nums.len() / 2) as nat;
        if nums.len() % 2 == 0 {
            Self::conc_val_taken(nums, taken)
        } else {
            Self::conc_val_taken(nums, taken) + nums[(nums.len() / 2) as int] as int
        }
    }
}

impl Solution {
    pub fn find_the_array_conc_val(nums: Vec<i32>) -> (result: i64)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10_000,
        ensures
            result as int == Self::conc_val_spec(nums@),
    {
        let mut i: usize = 0;
        let mut j: usize = nums.len() - 1;
        let mut total: i64 = 0;

        while i < j
            invariant
                0 <= i <= nums.len(),
                0 <= j < nums.len(),
                0 <= j as int,
                (j as int) < nums.len(),
                i <= j + 1,
                i + j + 1 == nums.len(),
                1 <= nums.len() <= 1000,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 10_000,
                total as int == Self::conc_val_taken(nums@, i as nat),
                0 <= total as int,
                total as int <= i as int * 1000010000int,
            decreases nums.len() - i,
        {
            let mut mul: i64 = 10;
            let mut x = nums[j] / 10;
            while x > 0
                invariant
                    0 <= j as int,
                    (j as int) < nums.len(),
                    1 <= nums@[j as int] <= 10_000,
                    x >= 0,
                    mul == 10 || mul == 100 || mul == 1000 || mul == 10000 || mul == 100000,
                    x as int == if mul == 10 {
                        nums@[j as int] as int / 10
                    } else if mul == 100 {
                        nums@[j as int] as int / 100
                    } else if mul == 1000 {
                        nums@[j as int] as int / 1000
                    } else if mul == 10000 {
                        nums@[j as int] as int / 10000
                    } else {
                        nums@[j as int] as int / 100000
                    },
                    nums@[j as int] as int / (mul as int / 10) > 0,
                decreases x,
            {
                proof {
                    if mul == 100000 {
                        assert(x as int == nums@[j as int] as int / 100000);
                        assert(nums@[j as int] as int / 100000 == 0);
                    }
                }
                let ghost old_mul = mul;
                let ghost old_x = x;
                mul = mul.wrapping_mul(10);
                x = x / 10;
                proof {
                    assert(old_mul == 10 || old_mul == 100 || old_mul == 1000 || old_mul == 10000);
                    assert(mul == 100 || mul == 1000 || mul == 10000 || mul == 100000);
                    if old_mul == 10 {
                        assert(old_x as int == nums@[j as int] as int / 10);
                        assert(x as int == nums@[j as int] as int / 100);
                    } else if old_mul == 100 {
                        assert(old_x as int == nums@[j as int] as int / 100);
                        assert(x as int == nums@[j as int] as int / 1000);
                    } else if old_mul == 1000 {
                        assert(old_x as int == nums@[j as int] as int / 1000);
                        assert(x as int == nums@[j as int] as int / 10000);
                    } else {
                        assert(old_mul == 10000);
                        assert(old_x as int == nums@[j as int] as int / 10000);
                        assert(x as int == nums@[j as int] as int / 100000);
                    }
                    assert(nums@[j as int] as int / (mul as int / 10) > 0);
                }
            }
            proof {
                assert(x == 0);
                if nums@[j as int] < 10 {
                    assert(nums@[j as int] as int / 10 == 0);
                    assert(mul == 10);
                } else if nums@[j as int] < 100 {
                    assert(nums@[j as int] as int / 10 > 0);
                    assert(nums@[j as int] as int / 100 == 0);
                    assert(mul == 100);
                } else if nums@[j as int] < 1000 {
                    assert(nums@[j as int] as int / 100 > 0);
                    assert(nums@[j as int] as int / 1000 == 0);
                    assert(mul == 1000);
                } else if nums@[j as int] < 10000 {
                    assert(nums@[j as int] as int / 1000 > 0);
                    assert(nums@[j as int] as int / 10000 == 0);
                    assert(mul == 10000);
                } else {
                    assert(nums@[j as int] == 10000);
                    assert(nums@[j as int] as int / 10000 > 0);
                    assert(nums@[j as int] as int / 100000 == 0);
                    assert(mul == 100000);
                }
                assert(Self::concat_num_spec(nums@[i as int] as int, nums@[j as int] as int)
                    == nums@[i as int] as int * mul as int + nums@[j as int] as int);
                assert(0 <= Self::concat_num_spec(nums@[i as int] as int, nums@[j as int] as int));
                assert(Self::concat_num_spec(nums@[i as int] as int, nums@[j as int] as int) <= 1000010000int);
                assert(Self::conc_val_taken(nums@, (i + 1) as nat)
                    == Self::conc_val_taken(nums@, i as nat)
                        + Self::concat_num_spec(nums@[i as int] as int, nums@[j as int] as int));
            }
            let ghost left_num = nums@[i as int];
            let ghost right_num = nums@[j as int];
            let ghost old_total = total;
            total = total.wrapping_add((nums[i] as i64).wrapping_mul(mul).wrapping_add(nums[j] as i64));
            proof {
                assert(total == old_total.wrapping_add((left_num as i64).wrapping_mul(mul).wrapping_add(right_num as i64)));
                assert(((left_num as i64).wrapping_mul(mul).wrapping_add(right_num as i64)) as int
                    == Self::concat_num_spec(left_num as int, right_num as int));
                assert(old_total as int == Self::conc_val_taken(nums@, i as nat));
                assert(0 <= old_total as int);
                assert(old_total as int <= i as int * 1000010000int);
                assert(0 <= ((left_num as i64).wrapping_mul(mul).wrapping_add(right_num as i64)) as int);
                assert(((left_num as i64).wrapping_mul(mul).wrapping_add(right_num as i64)) as int <= 1000010000int);
                assert(old_total as int + ((left_num as i64).wrapping_mul(mul).wrapping_add(right_num as i64)) as int <= i64::MAX);
                assert(total as int == old_total as int + ((left_num as i64).wrapping_mul(mul).wrapping_add(right_num as i64)) as int);
                assert(total as int == Self::conc_val_taken(nums@, (i + 1) as nat));
                assert(total as int <= (i as int + 1) * 1000010000int);
            }
            i = i + 1;
            j = j - 1;
        }

        if i == j {
            total = total.wrapping_add(nums[i] as i64);
            proof {
                assert(i + j + 1 == nums.len());
                assert(Self::conc_val_spec(nums@)
                    == Self::conc_val_taken(nums@, i as nat) + nums@[i as int] as int);
                assert(total as int == Self::conc_val_spec(nums@));
            }
        } else {
            proof {
                assert(i == j + 1);
                assert(i + j + 1 == nums.len());
                assert(2 * i == nums.len());
                assert(nums.len() % 2 == 0);
                assert(Self::conc_val_spec(nums@) == Self::conc_val_taken(nums@, i as nat));
                assert(total as int == Self::conc_val_spec(nums@));
            }
        }

        total
    }
}

}
