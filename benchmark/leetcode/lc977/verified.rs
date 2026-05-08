use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_eq_range(s: Seq<i32>, v: i32, lo: int, hi: int) -> int
        recommends 0 <= lo, hi <= s.len()
        decreases hi - lo
    {
        if lo >= hi { 0 }
        else {
            (if s[lo] == v { 1int } else { 0int }) + Self::count_eq_range(s, v, lo + 1, hi)
        }
    }

    pub open spec fn count_sq_eq_range(s: Seq<i32>, v: i32, lo: int, hi: int) -> int
        recommends 0 <= lo, hi <= s.len()
        decreases hi - lo
    {
        if lo >= hi { 0 }
        else {
            (if s[lo] * s[lo] == v { 1int } else { 0int }) + Self::count_sq_eq_range(s, v, lo + 1, hi)
        }
    }

    proof fn lemma_max_square_at_ends(nums: Seq<i32>, left: int, right: int, m: int)
        requires
            0 <= left <= m <= right < nums.len(),
            forall |i: int, j: int| 0 <= i <= j < nums.len() ==> nums[i] <= nums[j],
        ensures
            nums[m] * nums[m] <= nums[left] * nums[left] || nums[m] * nums[m] <= nums[right] * nums[right],
    {
        if nums[m] >= 0 {
            assert(nums[m] * nums[m] <= nums[right] * nums[right]) by(nonlinear_arith)
                requires 0 <= nums[m], nums[m] <= nums[right];
        } else {
            assert(nums[m] * nums[m] <= nums[left] * nums[left]) by(nonlinear_arith)
                requires nums[left] <= nums[m], nums[m] < 0;
        }
    }

    proof fn lemma_square_bound(x: i32)
        requires
            -10_000 <= x <= 10_000,
        ensures
            0 <= x * x <= 100_000_000,
    {
        assert(0 <= x * x) by(nonlinear_arith)
            requires -10_000 <= x, x <= 10_000;
        assert(x * x <= 100_000_000) by(nonlinear_arith)
            requires -10_000 <= x, x <= 10_000;
    }

    proof fn lemma_count_sq_eq_range_right_ext(s: Seq<i32>, v: i32, lo: int, hi: int)
        requires 0 <= lo, lo <= hi, hi < s.len()
        ensures Self::count_sq_eq_range(s, v, lo, hi + 1)
            == Self::count_sq_eq_range(s, v, lo, hi) + (if s[hi] * s[hi] == v { 1int } else { 0int })
        decreases hi - lo
    {
        if lo == hi {
            assert(Self::count_sq_eq_range(s, v, lo + 1, lo + 1) == 0int);
            assert(Self::count_sq_eq_range(s, v, lo, lo) == 0int);
        } else {
            Self::lemma_count_sq_eq_range_right_ext(s, v, lo + 1, hi);
        }
    }

    proof fn lemma_count_eq_range_update(s: Seq<i32>, v: i32, lo: int, hi: int, pos: int, val: i32)
        requires 0 <= lo, lo <= hi, hi <= s.len(), 0 <= pos < s.len(), pos < lo || pos >= hi
        ensures Self::count_eq_range(s.update(pos, val), v, lo, hi) == Self::count_eq_range(s, v, lo, hi)
        decreases hi - lo
    {
        if lo >= hi {
        } else {
            assert(s.update(pos, val)[lo] == s[lo]);
            Self::lemma_count_eq_range_update(s, v, lo + 1, hi, pos, val);
        }
    }

    proof fn lemma_count_sq_eq_range_split(s: Seq<i32>, v: i32, lo: int, mid: int, hi: int)
        requires 0 <= lo, lo <= mid, mid <= hi, hi <= s.len()
        ensures Self::count_sq_eq_range(s, v, lo, hi)
            == Self::count_sq_eq_range(s, v, lo, mid) + Self::count_sq_eq_range(s, v, mid, hi)
        decreases mid - lo
    {
        if lo >= mid {
        } else {
            Self::lemma_count_sq_eq_range_split(s, v, lo + 1, mid, hi);
        }
    }

    pub fn sorted_squares(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 10_000,
            forall |i: int| 0 <= i < nums.len() ==> -10_000 <= #[trigger] nums[i] <= 10_000,
            forall |i: int, j: int| 0 <= i <= j < nums.len() ==> nums[i] <= nums[j],
        ensures
            result.len() == nums.len(),
            forall |i: int, j: int| 0 <= i <= j < result.len() as int ==> result[i] <= result[j],
            forall |v: i32| Self::count_eq_range(result@, v, 0, result.len() as int)
                == Self::count_sq_eq_range(nums@, v, 0, nums.len() as int),
    {
        let n = nums.len();
        let mut result: Vec<i32> = Vec::with_capacity(n);

        let mut init_k: usize = 0;
        while init_k < n
            invariant
                n == nums.len(),
                result.len() == init_k,
                init_k <= n,
            decreases n - init_k,
        {
            result.push(0i32);
            init_k = init_k + 1;
        }

        let mut k: usize = 0;
        let mut left: usize = 0;

        while k < n
            invariant
                n == result.len(),
                n == nums.len(),
                1 <= n <= 10_000,
                0 <= k <= n,
                0 <= left <= k,
                forall |i: int| 0 <= i < nums.len() ==> -10_000 <= #[trigger] nums[i] <= 10_000,
                forall |i: int, j: int| 0 <= i <= j < nums.len() ==> nums[i] <= nums[j],
                forall |i: int, j: int| #![trigger result[i], result[j]]
                    (n - k) as int <= i && i <= j && j < n as int ==> result[i] <= result[j],
                k > 0 ==> (forall |m: int| #![trigger nums[m]] left as int <= m <= (n as int - 1 - k as int + left as int) ==>
                    nums[m] * nums[m] <= result[(n - k) as int]),
                forall |v: i32| #![auto]
                    Self::count_eq_range(result@, v, (n - k) as int, n as int)
                    == Self::count_sq_eq_range(nums@, v, 0, left as int)
                     + Self::count_sq_eq_range(nums@, v, (n as int - k as int + left as int), n as int),
            decreases n - k,
        {
            let right: usize = n - 1 - k + left;
            let pos: usize = n - 1 - k;

            proof {
                Self::lemma_square_bound(nums[left as int]);
                Self::lemma_square_bound(nums[right as int]);
            }

            let left_sq: i32 = nums[left] * nums[left];
            let right_sq: i32 = nums[right] * nums[right];

            let ghost before = result@;
            let ghost old_left = left as int;
            let ghost old_k = k as int;
            let ghost old_right = right as int;

            if left_sq > right_sq {
                result.set(pos, left_sq);
                left = left + 1;

                proof {
                    assert(result@ =~= before.update(pos as int, left_sq));

                    
                    assert forall |m: int| #![trigger nums[m]] left as int <= m <= old_right
                        implies nums[m] * nums[m] <= left_sq by {
                        Self::lemma_max_square_at_ends(nums@, old_left, old_right, m);
                    };

                    
                    if old_k > 0 {
                        assert(nums[old_left] * nums[old_left] <= before[(n as int - old_k) as int]);
                    }
                    assert forall |i: int, j: int|
                        #![trigger result[i], result[j]]
                        pos as int <= i && i <= j && j < n as int
                        implies result[i] <= result[j] by {
                        if i == pos as int && j > pos as int {
                            if old_k > 0 {
                                assert(result[j] == before[j]);
                                assert(left_sq <= before[(n as int - old_k) as int]);
                                assert(before[(n as int - old_k) as int] <= before[j]);
                            }
                        } else if i > pos as int {
                            assert(result[i] == before[i]);
                            assert(result[j] == before[j]);
                        }
                    };

                    
                    assert forall |v: i32| #![auto]
                        Self::count_eq_range(result@, v, pos as int, n as int)
                        == Self::count_sq_eq_range(nums@, v, 0, left as int)
                         + Self::count_sq_eq_range(nums@, v, (n as int - old_k + old_left), n as int)
                    by {
                        Self::lemma_count_eq_range_update(before, v, pos as int + 1, n as int, pos as int, left_sq);
                        Self::lemma_count_sq_eq_range_right_ext(nums@, v, 0, old_left);
                    };
                }
            } else {
                result.set(pos, right_sq);

                proof {
                    assert(result@ =~= before.update(pos as int, right_sq));

                    
                    if old_left < old_right {
                        assert forall |m: int| #![trigger nums[m]] old_left <= m <= old_right - 1
                            implies nums[m] * nums[m] <= right_sq by {
                            Self::lemma_max_square_at_ends(nums@, old_left, old_right, m);
                        };
                    }

                    
                    if old_k > 0 {
                        assert(nums[old_right] * nums[old_right] <= before[(n as int - old_k) as int]);
                    }
                    assert forall |i: int, j: int|
                        #![trigger result[i], result[j]]
                        pos as int <= i && i <= j && j < n as int
                        implies result[i] <= result[j] by {
                        if i == pos as int && j > pos as int {
                            if old_k > 0 {
                                assert(result[j] == before[j]);
                                assert(right_sq <= before[(n as int - old_k) as int]);
                                assert(before[(n as int - old_k) as int] <= before[j]);
                            }
                        } else if i > pos as int {
                            assert(result[i] == before[i]);
                            assert(result[j] == before[j]);
                        }
                    };

                    
                    assert forall |v: i32| #![auto]
                        Self::count_eq_range(result@, v, pos as int, n as int)
                        == Self::count_sq_eq_range(nums@, v, 0, left as int)
                         + Self::count_sq_eq_range(nums@, v, old_right, n as int)
                    by {
                        Self::lemma_count_eq_range_update(before, v, pos as int + 1, n as int, pos as int, right_sq);
                    };
                }
            }

            k = k + 1;
        }

        
        proof {
            assert(k == n);
            assert forall |v: i32| #![auto]
                Self::count_eq_range(result@, v, 0, n as int)
                == Self::count_sq_eq_range(nums@, v, 0, n as int)
            by {
                Self::lemma_count_sq_eq_range_split(nums@, v, 0, left as int, n as int);
            };
        }

        result
    }
}

}
