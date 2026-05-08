use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn circ_idx(n: int, i: int, k: int) -> int
    decreases 0int
{
    if i + k < n {
        i + k
    } else {
        i + k - n
    }
}

pub open spec fn is_next_greater(nums: Seq<i32>, res: Seq<i32>, i: int) -> bool
    decreases 0int
{
    let n = nums.len() as int;
    0 <= i < n
    && (
        (res[i] == -1
         && forall |k: int| 1 <= k < n ==> nums[circ_idx(n, i, k)] <= nums[i])
        || (res[i] != -1
            && res[i] > nums[i]
            && exists |k: int|
                1 <= k < n
                && nums[circ_idx(n, i, k)] == res[i]
                && forall |j: int| 1 <= j < k ==> nums[circ_idx(n, i, j)] <= nums[i])
    )
}

proof fn lemma_circ_idx_mod(n: int, i: int, k: int)
    requires
        0 < n,
        0 <= i < n,
        1 <= k < n,
    ensures
        circ_idx(n, i, k) == (i + k) % n,
{
    if i + k < n {
        lemma_small_mod((i + k) as nat, n as nat);
    } else {
        assert(i + k >= n);
        let r = i + k - n;
        assert(r >= 0);
        assert(r < n);
        lemma_small_mod(r as nat, n as nat);
        lemma_mod_add_multiples_vanish(r, n);
        assert((i + k) % n == (n + r) % n);
        assert((n + r) % n == r % n);
        assert(r % n == r);
        assert(circ_idx(n, i, k) == r);
    }
}

proof fn lemma_circ_idx_range(n: int, i: int, k: int)
    requires
        0 <= i < n,
        1 <= k < n,
    ensures
        0 <= circ_idx(n, i, k) < n,
{
    lemma_circ_idx_mod(n, i, k);
    lemma_mod_division_less_than_divisor(i + k, n);
}

proof fn lemma_seq_update_at(s: Seq<i32>, i: int, a: i32)
    requires
        0 <= i < s.len(),
    ensures
        s.update(i, a)[i] == a,
{
    broadcast use vstd::seq::group_seq_axioms;
}

proof fn lemma_is_next_greater_preserved_update(nums: Seq<i32>, res: Seq<i32>, i: int, idx: int, v: i32)
    requires
        res.len() == nums.len(),
        0 <= i < res.len(),
        0 <= idx < res.len(),
        idx != i,
        is_next_greater(nums, res, idx),
    ensures
        is_next_greater(nums, res.update(i, v), idx),
{
    assert(res.update(i, v)[idx] == res[idx]);
}

proof fn lemma_circ_idx_when_lt(n: int, i: int, k: int)
    requires
        0 <= i < n,
        1 <= k < n,
        i + k < n,
    ensures
        circ_idx(n, i, k) == i + k,
{
    reveal(circ_idx);
}


proof fn lemma_usize_lt_to_int(i: usize, k: usize, n: usize)
    requires
        i + k < n,
        (i as int) + (k as int) <= 2 * (n as int),
    ensures
        (i as int) + (k as int) < (n as int),
        ((i + k) as int) == (i as int) + (k as int),
{
    assert((i + k) as int == (i as int) + (k as int)) by (bit_vector);
    assert(((i + k) as int) < (n as int));
}


impl Solution {
    pub fn next_greater_elements(nums: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= nums.len() <= 10_000,
            forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] != -1i32,
        ensures
            res.len() == nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> is_next_greater(nums@, res@, i),
    {
        let n = nums.len();
        let ghost n_int = n as int;
        proof {
            assert(1 <= n <= 10_000);
            assert(n_int == n as int);
            assert(1 <= n_int);
            assert(0 < n_int);
        }

        proof {
            assert forall |ii: int| 0 <= ii < nums@.len() implies nums@[ii] != (-1i32) by {
                assert(nums[ii] != (-1i32));
            };
        }

        let mut res: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                0 <= idx <= n,
                res.len() == idx,
                n == nums.len(),
                forall |k: int| 0 <= k < idx as int ==> res@[k] == -1,
            decreases n - idx
        {
            res.push(-1);
            idx = idx + 1;
        }
        proof {
            assert(res@.len() as int == n_int);
            assert(forall |k: int| 0 <= k < n_int ==> res@[k] == -1);
        }
        let mut i: usize = 0;
        let ghost mut res_at_start = res@;
        let ghost mut old_i: int = -1;
        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                n <= 10_000,
                res@.len() as int == n_int,
                n_int == n as int,
                0 < n_int,
                (i as int) >= 0 && (i as int) <= n_int,
                old_i == (i as int) - 1,
                forall |idx: int| 0 <= idx < (i as int) ==> is_next_greater(nums@, res@, idx),
                forall |idx: int| (i as int) < idx < n_int ==> res@[idx] == -1,
                forall |idx: int| old_i < idx < n_int ==> res@[idx] == -1,
                res_at_start.len() == n_int,
                forall |idx: int| (i as int) < idx < n_int ==> res_at_start[idx] == -1,
                forall |idx: int| (i as int) < idx < n_int ==> res@[idx] == res_at_start[idx],
                forall |ii: int| 0 <= ii < nums@.len() ==> nums@[ii] != (-1i32),
            decreases n - i
        {
            proof {
                assert(old_i == (i as int) - 1);
                assert(old_i < (i as int));
                assert((i as int) < n_int);
                assert(res@[(i as int)] == -1);
            }
            let ghost i_int = i as int;
            proof {
                assert(0 <= i_int);
                assert(i_int < (res@.len() as int));
                assert(i_int < (nums@.len() as int));
            }
            let mut k: usize = 1;
            while k < n
                invariant
                    1 <= k <= n,
                    i < n,
                    n == nums.len(),
                    n <= 10_000,
                    res@.len() as int == n_int,
                    0 <= i_int < n_int,
                    (i as int) == i_int,
                    i_int < (res@.len() as int),
                    n_int == n as int,
                    nums@.len() as int == n_int,
                    forall |idx: int| 0 <= idx < i_int ==> is_next_greater(nums@, res@, idx),
                    forall |idx: int| (i as int) < idx < n_int ==> res@[idx] == -1,
                    (k as int) < n_int ==> res@[i_int] == -1,
                    res@[i_int] == -1 ==> forall |j: int| 1 <= j < (k as int) ==> nums@[circ_idx(n_int, i_int, j)] <= nums@[i_int],
                    res@[i_int] != -1 ==> is_next_greater(nums@, res@, i_int),
                    (i as int) + (k as int) <= 2 * n_int,
                    forall |ii: int| 0 <= ii < nums@.len() ==> nums@[ii] != (-1i32),
                decreases n - k
            {
                assert((i as int) + (k as int) <= 2 * n_int);
                assert(n_int <= 10000);
                assert(2 * n_int <= 20000);
                assert((i as int) + (k as int) < 0x1_0000_0000) by (nonlinear_arith)
                    requires (i as int) + (k as int) <= 20_000
                {}
                let j = if i + k < n { i + k } else { i + k - n };
                proof {
                    assert(k < n);
                    assert(n_int == n as int);
                    assert(1 <= (k as int));
                    assert((k as int) < (n as int));
                    assert((k as int) < n_int);
                    lemma_circ_idx_mod(n_int, i_int, k as int);
                    lemma_circ_idx_range(n_int, i_int, k as int);
                    if i + k < n {
                        lemma_usize_lt_to_int(i, k, n);
                        lemma_circ_idx_when_lt(n_int, i as int, k as int);
                        assert(j == i + k);
                        assert((j as int) == (i as int) + (k as int));
                        assert((j as int) == circ_idx(n_int, i as int, k as int));
                        assert(circ_idx(n_int, i as int, k as int) == circ_idx(n_int, i_int, k as int));
                        assert((j as int) == circ_idx(n_int, i_int, k as int));
                    } else {
                        assert((i as int) + (k as int) >= n_int);
                        lemma_circ_idx_mod(n_int, i_int, k as int);
                        lemma_mod_add_multiples_vanish((i as int) + (k as int) - n_int, n_int);
                        lemma_small_mod(((i as int) + (k as int) - n_int) as nat, n_int as nat);
                        assert(circ_idx(n_int, i_int, k as int) == (i as int) + (k as int) - n_int);
                        assert(j == i + k - n);
                        assert((j as int) == (i as int) + (k as int) - n_int);
                        assert((j as int) == circ_idx(n_int, i_int, k as int));
                    }
                    assert((j as int) == circ_idx(n_int, i_int, k as int));
                }
                assert(i < n);
                assert(j < n);
                let ghost res_before = res@;
                assert(-1 == 0 - 1);
                assert(res@[i_int] == 0 - 1);
                assert(res_before[i_int] == 0 - 1);
                if nums[j] > nums[i] {
                    res[i] = nums[j];
                    proof {
                        let ghost val = nums@[j as int];
                        let ghost res_updated = res_before.update(i_int, val);
                        assert(res@ == res_updated);

                        lemma_seq_update_at(res_before, i_int, val);
                        assert(res_updated[i_int] == val);
                        assert(res@[i_int] == val);

                        assert(forall |idx: int| 0 <= idx < n_int && idx != i_int ==> res@[idx] == res_before[idx]);
                        assert(forall |idx: int| (i as int) < idx < n_int ==> res@[idx] == -1);

                        assert(0 <= (j as int) < nums@.len());
                        assert(nums@[j as int] != (-1i32));
                        assert(val != (-1i32));
                        assert(res_updated[i_int] != (-1i32));

                        assert(val > nums@[i_int]);
                        assert(res_updated[i_int] > nums@[i_int]);

                        assert((j as int) == circ_idx(n_int, i_int, k as int));
                        lemma_circ_idx_range(n_int, i_int, k as int);
                        assert(nums@[circ_idx(n_int, i_int, k as int)] == val);
                        assert(nums@[circ_idx(n_int, i_int, k as int)] == res_updated[i_int]);

                        assert(1 <= (k as int) && (k as int) < n_int);
                        assert(forall |jj: int| 1 <= jj < (k as int) ==> nums@[circ_idx(n_int, i_int, jj)] <= nums@[i_int]);

                        reveal_with_fuel(is_next_greater, 1);
                        reveal_with_fuel(circ_idx, 1);
                        assert(is_next_greater(nums@, res_updated, i_int));
                        assert(is_next_greater(nums@, res@, i_int));
                        assert forall |idx: int| 0 <= idx < i_int implies is_next_greater(nums@, res@, idx) by {
                            lemma_is_next_greater_preserved_update(nums@, res_before, i_int, idx, val);
                        }
                    }
                    k = n;
                } else {
                    proof {
                        assert(nums@[circ_idx(n_int, i_int, k as int)] <= nums@[i_int]);
                    }
                    k = k + 1;
                }
            }
            proof {
                assert(res@[i_int] == -1 ==> forall |j: int| 1 <= j < n_int ==> nums@[circ_idx(n_int, i_int, j)] <= nums@[i_int]);
                assert(is_next_greater(nums@, res@, i_int));
                assert((i as int) == i_int);
                assert((i as int) + 1 < n_int ==> res@[(i as int) + 1] == -1);
                old_i = i as int;
            }
            i = i + 1;
        }
        proof {
            assert(forall |idx: int| 0 <= idx < n_int ==> is_next_greater(nums@, res@, idx));
        }
        res
    }
}

}