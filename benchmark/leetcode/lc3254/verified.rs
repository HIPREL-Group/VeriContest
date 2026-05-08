use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn consecutive_step(nums: Seq<i32>, i: int) -> bool
        recommends
            0 <= i + 1 < nums.len(),
    {
        nums[i + 1] == nums[i] + 1
    }

    pub open spec fn window_has_power(nums: Seq<i32>, start: int, k: int) -> bool
        recommends
            0 <= start,
            1 <= k,
            start + k <= nums.len(),
    {
        forall |j: int| start <= j < start + k - 1 ==> #[trigger] Self::consecutive_step(nums, j)
    }

    pub open spec fn window_power(nums: Seq<i32>, start: int, k: int) -> int
        recommends
            0 <= start,
            1 <= k,
            start + k <= nums.len(),
    {
        if Self::window_has_power(nums, start, k) {
            nums[start + k - 1] as int
        } else {
            -1
        }
    }

    pub fn results_array(nums: Vec<i32>, k: i32) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 500,
            1 <= k <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
        ensures
            result@.len() == nums.len() as int - k as int + 1,
            forall |i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] as int == Self::window_power(nums@, i, k as int),
    {
        let n = nums.len();
        let k_usize = k as usize;
        let mut result: Vec<i32> = Vec::new();
        let mut run_len: usize = 1;
        if k_usize == 1 {
            result.push(nums[0]);
            proof {
                assert(Self::window_has_power(nums@, 0, 1)) by {
                    assert forall |j: int| 0 <= j < 0 implies #[trigger] Self::consecutive_step(nums@, j) by {
                    }
                };
                assert(Self::window_power(nums@, 0, 1) == nums[0] as int);
                assert forall |s: int| 0 <= s < result@.len() implies #[trigger] result@[s] as int == Self::window_power(nums@, s, k as int) by {
                    assert(s == 0);
                }
            }
        }
        let mut i: usize = 1;
        while i < n
            invariant
                n == nums.len(),
                1 <= nums.len() <= 500,
                1 <= k <= nums.len(),
                k_usize == k as usize,
                1 <= k_usize <= n,
                1 <= i <= n,
                1 <= run_len <= i,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 100_000,
                forall |j: int| i as int - run_len as int <= j < i as int - 1 ==> #[trigger] Self::consecutive_step(nums@, j),
                run_len as int >= i as int || !(#[trigger] Self::consecutive_step(nums@, i as int - run_len as int - 1)),
                k_usize != 1 || result@.len() == i as int,
                !(k_usize > 1 && i < k_usize) || result@.len() == 0,
                !(k_usize > 1 && k_usize <= i) || result@.len() == i as int - k as int + 1,
                forall |s: int| 0 <= s < result@.len() ==> #[trigger] result@[s] as int == Self::window_power(nums@, s, k as int),
            decreases n - i,
        {
            let prev_val = nums[i - 1];
            let curr_val = nums[i];
            let prev_run_len = run_len;
            if prev_val + 1 == curr_val {
                proof {
                    assert(prev_run_len <= i);
                }
                run_len = prev_run_len + 1;
            } else {
                run_len = 1;
            }
            proof {
                let i_int = i as int;
                let run_len_int = run_len as int;
                let prev_run_len_int = prev_run_len as int;
                if prev_val + 1 == curr_val {
                    assert forall |j: int| i_int + 1 - run_len_int <= j < i_int implies #[trigger] Self::consecutive_step(nums@, j) by {
                        if j < i_int - 1 {
                            assert(i_int - prev_run_len_int <= j < i_int - 1);
                        } else {
                            assert(j == i_int - 1);
                            assert(Self::consecutive_step(nums@, j));
                        }
                    };
                    if run_len_int < i_int + 1 {
                        assert(prev_run_len_int < i_int);
                        assert(i_int - run_len_int == i_int - prev_run_len_int - 1);
                        assert(!Self::consecutive_step(nums@, i_int - run_len_int));
                    }
                } else {
                    assert forall |j: int| i_int + 1 - run_len_int <= j < i_int implies #[trigger] Self::consecutive_step(nums@, j) by {
                    };
                    assert(run_len_int < i_int + 1);
                    assert(!Self::consecutive_step(nums@, i_int - run_len_int));
                }
            }
            if i + 1 >= k_usize {
                let out = if run_len >= k_usize { curr_val } else { -1 };
                proof {
                    let i_int = i as int;
                    let run_len_int = run_len as int;
                    let start = i_int + 1 - k as int;
                    if run_len >= k_usize {
                        assert(Self::window_has_power(nums@, start, k as int)) by {
                            assert forall |j: int| start <= j < start + k as int - 1 implies #[trigger] Self::consecutive_step(nums@, j) by {
                                assert(i_int + 1 - run_len_int <= start);
                                assert(start + k as int - 1 == i_int);
                                assert(i_int + 1 - run_len_int <= j < i_int);
                            }
                        };
                        assert(out == curr_val);
                        assert(Self::window_power(nums@, start, k as int) == curr_val as int);
                    } else {
                        assert(k_usize > 1);
                        let bad = i_int - run_len_int;
                        assert(start <= bad < i_int);
                        assert(!Self::window_has_power(nums@, start, k as int)) by {
                            if Self::window_has_power(nums@, start, k as int) {
                                assert(Self::consecutive_step(nums@, bad));
                                assert(!Self::consecutive_step(nums@, bad));
                                assert(false);
                            }
                        };
                        assert(out == -1);
                        assert(Self::window_power(nums@, start, k as int) == -1);
                    }
                }
                let ghost old_result = result@;
                result.push(out);
                proof {
                    let i_int = i as int;
                    let start = i_int + 1 - k as int;
                    assert(result@ == old_result.push(out));
                    assert forall |s: int| 0 <= s < result@.len() implies #[trigger] result@[s] as int == Self::window_power(nums@, s, k as int) by {
                        if s < old_result.len() {
                            assert(result@[s] == old_result[s]);
                        } else {
                            assert(s == old_result.len());
                            assert(old_result.len() == start);
                            assert(result@[s] == out);
                        }
                    };
                    if k_usize == 1 {
                        assert(old_result.len() == i_int);
                        assert(result@.len() == i_int + 1);
                    } else if i == k_usize - 1 {
                        assert(old_result.len() == 0);
                        assert(result@.len() == 1);
                    } else {
                        assert(old_result.len() == i_int - k as int + 1);
                        assert(result@.len() == i_int - k as int + 2);
                    }
                }
            }
            i += 1;
        }
        result
    }
}

}