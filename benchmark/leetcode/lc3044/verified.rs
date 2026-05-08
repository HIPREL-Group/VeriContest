use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn check_no_divisor(n: int, d: int) -> bool {
        n % d != 0
    }

    pub open spec fn prime_int(n: int) -> bool {
        n > 1 && forall|d: int| 2 <= d && d * d <= n ==> #[trigger] Self::check_no_divisor(n, d)
    }

    pub open spec fn is_candidate_prime(n: int) -> bool {
        n > 10 && Self::prime_int(n)
    }

    pub open spec fn row_delta(d: int) -> int {
        if d == 0 {
            0
        } else if d == 1 {
            1
        } else if d == 2 {
            1
        } else if d == 3 {
            1
        } else if d == 4 {
            0
        } else if d == 5 {
            -1
        } else if d == 6 {
            -1
        } else {
            -1
        }
    }

    pub open spec fn col_delta(d: int) -> int {
        if d == 0 {
            1
        } else if d == 1 {
            1
        } else if d == 2 {
            0
        } else if d == 3 {
            -1
        } else if d == 4 {
            -1
        } else if d == 5 {
            -1
        } else if d == 6 {
            0
        } else {
            1
        }
    }

    pub open spec fn row_at(r: int, d: int, step: int) -> int {
        r + step * Self::row_delta(d)
    }

    pub open spec fn col_at(c: int, d: int, step: int) -> int {
        c + step * Self::col_delta(d)
    }

    pub open spec fn in_bounds(mat: Seq<Vec<i32>>, rr: int, cc: int) -> bool {
        mat.len() > 0 && 0 <= rr < mat.len() && 0 <= cc < mat[0].len() as int
    }

    pub open spec fn path_valid(mat: Seq<Vec<i32>>, r: int, c: int, d: int, step: int) -> bool {
        0 <= step <= 5 && mat.len() > 0 && forall|t: int| 0 <= t <= step ==> Self::in_bounds(mat, Self::row_at(r, d, t), Self::col_at(c, d, t))
    }

    pub open spec fn number_on_path(mat: Seq<Vec<i32>>, r: int, c: int, d: int, step: int) -> int
        decreases step
    {
        if step <= 0 {
            mat[r][c] as int
        } else {
            Self::number_on_path(mat, r, c, d, step - 1) * 10 + mat[Self::row_at(r, d, step)][Self::col_at(c, d, step)] as int
        }
    }

    pub open spec fn direction_numbers_upto(mat: Seq<Vec<i32>>, r: int, c: int, d: int, step_bound: int) -> Seq<i32>
        decreases step_bound
    {
        if step_bound <= 0 {
            seq![]
        } else {
            let prev = Self::direction_numbers_upto(mat, r, c, d, step_bound - 1);
            if Self::path_valid(mat, r, c, d, step_bound) {
                prev.push(Self::number_on_path(mat, r, c, d, step_bound) as i32)
            } else {
                prev
            }
        }
    }

    pub open spec fn cell_numbers_upto(mat: Seq<Vec<i32>>, r: int, c: int, d_bound: int) -> Seq<i32>
        decreases d_bound
    {
        if d_bound <= 0 {
            seq![]
        } else {
            Self::cell_numbers_upto(mat, r, c, d_bound - 1) + Self::direction_numbers_upto(mat, r, c, d_bound - 1, 5)
        }
    }

    pub open spec fn all_numbers_upto(mat: Seq<Vec<i32>>, idx_bound: int) -> Seq<i32>
        decreases idx_bound
    {
        if idx_bound <= 0 || mat.len() == 0 || mat[0].len() == 0 {
            seq![]
        } else {
            let prev = Self::all_numbers_upto(mat, idx_bound - 1);
            let idx = idx_bound - 1;
            if 0 <= idx < (mat.len() * mat[0].len()) as int {
                prev + Self::cell_numbers_upto(mat, idx / (mat[0].len() as int), idx % (mat[0].len() as int), 8)
            } else {
                prev
            }
        }
    }

    pub open spec fn all_numbers(mat: Seq<Vec<i32>>) -> Seq<i32> {
        if mat.len() == 0 || mat[0].len() == 0 {
            seq![]
        } else {
            Self::all_numbers_upto(mat, (mat.len() * mat[0].len()) as int)
        }
    }

    pub open spec fn count_occurrences(s: Seq<i32>, value: i32) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            Self::count_occurrences(s.drop_last(), value) + if s.last() == value { 1 as nat } else { 0 as nat }
        }
    }

    proof fn lemma_count_extend(s: Seq<i32>, value: i32, elem: i32)
        ensures
            Self::count_occurrences(s.push(elem), value) ==
                Self::count_occurrences(s, value) + if elem == value { 1 as nat } else { 0 as nat },
    {
        assert(s.push(elem).drop_last() =~= s);
    }

    pub open spec fn max_path_num(step: int) -> int
        decreases step,
    {
        if step <= 0 { 9 }
        else { Self::max_path_num(step - 1) * 10 + 9 }
    }

    proof fn lemma_max_path_num_bound(step: int)
        requires 0 <= step <= 5,
        ensures Self::max_path_num(step) <= 999_999,
    {
        assert(Self::max_path_num(0) == 9);
        assert(Self::max_path_num(1) == 99);
        assert(Self::max_path_num(2) == 999);
        assert(Self::max_path_num(3) == 9999);
        assert(Self::max_path_num(4) == 99999);
        assert(Self::max_path_num(5) == 999999);
    }

    fn get_dx(d: usize) -> (res: i32)
        requires 0 <= d < 8,
        ensures -1 <= res <= 1, res as int == Self::row_delta(d as int),
    {
        if d == 0 { 0 } else if d == 1 { 1 } else if d == 2 { 1 } else if d == 3 { 1 }
        else if d == 4 { 0 } else if d == 5 { -1 } else if d == 6 { -1 } else { -1 }
    }

    fn get_dy(d: usize) -> (res: i32)
        requires 0 <= d < 8,
        ensures -1 <= res <= 1, res as int == Self::col_delta(d as int),
    {
        if d == 0 { 1 } else if d == 1 { 1 } else if d == 2 { 0 } else if d == 3 { -1 }
        else if d == 4 { -1 } else if d == 5 { -1 } else if d == 6 { 0 } else { 1 }
    }

    proof fn lemma_max_path_num_positive(step: int)
        requires 0 <= step,
        ensures Self::max_path_num(step) >= 9,
        decreases step,
    {
        if step > 0 {
            Self::lemma_max_path_num_positive(step - 1);
        }
    }

    fn is_prime(num: i32) -> (res: bool)
        requires
            num >= 0,
            num <= 999_999,
        ensures
            res == Self::prime_int(num as int),
    {
        if num <= 1 {
            return false;
        }

        let mut d = 2;
        while d * d <= num
            invariant
                num >= 2,
                num <= 999_999,
                2 <= d,
                d <= 1000,
                d as int * d as int <= 1_000_000,
                forall|k: int| 2 <= k < d ==> #[trigger] Self::check_no_divisor(num as int, k),
            decreases num - d + 1,
        {
            assert(d as int <= num as int) by(nonlinear_arith)
                requires d as int >= 2, d as int * d as int <= num as int;
            if num % d == 0 {
                proof {
                    assert(2 <= d as int && d as int * d as int <= num as int);
                    assert(!Self::check_no_divisor(num as int, d as int));
                    assert(!Self::prime_int(num as int));
                }
                return false;
            }
            let old_d = d;
            d += 1;
            proof {
                assert(old_d as int * old_d as int <= num as int);
                assert(old_d <= 999) by(nonlinear_arith)
                    requires old_d as int * old_d as int <= 999_999int, old_d >= 2i32;
                assert(d <= 1000);
                assert(d as int * d as int <= 1_000_000) by(nonlinear_arith)
                    requires d as int <= 1000, d as int >= 2;
                assert forall|k: int| 2 <= k < d implies #[trigger] Self::check_no_divisor(num as int, k) by {
                    if k < old_d as int {
                    } else {
                        assert(k == old_d as int);
                        assert(num as int % k != 0);
                    }
                }
            }
        }

        proof {
            assert(num > 1);
            assert(d as int * d as int > num as int);
            assert forall|k: int| 2 <= k && k * k <= num as int implies #[trigger] Self::check_no_divisor(num as int, k) by {
                assert(k < d as int) by(nonlinear_arith)
                    requires
                        k >= 0,
                        d as int >= 2,
                        k * k <= num as int,
                        d as int * d as int > num as int;
            }
        }

        true
    }

    pub fn most_frequent_prime(mat: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= mat.len() <= 6,
            forall|i: int| 0 <= i < mat.len() ==> 1 <= #[trigger] mat[i].len() <= 6,
            forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() == mat[0].len(),
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[0].len() ==> 1 <= #[trigger] mat[i][j] <= 9,
        ensures
            ((res == -1) && (forall|k: int| 0 <= k < Self::all_numbers(mat@).len() ==> !Self::is_candidate_prime(#[trigger] Self::all_numbers(mat@)[k] as int))) ||
            (Self::is_candidate_prime(res as int) &&
             forall|k: int| 0 <= k < Self::all_numbers(mat@).len() && Self::is_candidate_prime(#[trigger] Self::all_numbers(mat@)[k] as int) ==>
                 (Self::count_occurrences(Self::all_numbers(mat@), Self::all_numbers(mat@)[k]) < Self::count_occurrences(Self::all_numbers(mat@), res) ||
                  (Self::count_occurrences(Self::all_numbers(mat@), Self::all_numbers(mat@)[k]) == Self::count_occurrences(Self::all_numbers(mat@), res) && Self::all_numbers(mat@)[k] <= res))),
    {
        let m = mat.len();
        let n = mat[0].len();
        assert(m * n <= 36) by(nonlinear_arith)
            requires 1 <= m <= 6usize, 1 <= n <= 6usize;
        let total = m * n;
        let dx = [0, 1, 1, 1, 0, -1, -1, -1];
        let dy = [1, 1, 0, -1, -1, -1, 0, 1];

        let mut nums: Vec<i32> = Vec::new();
        let mut idx = 0;
        while idx < total
            invariant
                m == mat.len(),
                n == mat[0].len(),
                total == m * n,
                1 <= m <= 6,
                1 <= n <= 6,
                total <= 36,
                0 <= idx <= total,
                forall|i: int| 0 <= i < mat.len() ==> 1 <= #[trigger] mat[i].len() <= 6,
                forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() == mat[0].len(),
                forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[0].len() ==> 1 <= #[trigger] mat[i][j] <= 9,
                nums@ == Self::all_numbers_upto(mat@, idx as int),
                forall|k: int| 0 <= k < nums.len() ==> 11 <= #[trigger] nums[k] <= 999_999,
                nums.len() as int <= idx as int * 40,
            decreases total - idx,
        {
            assert(idx / n < m) by(nonlinear_arith) requires 0 <= idx, idx < m * n, 1 <= n;
            assert(idx % n < n) by(nonlinear_arith) requires 0 <= idx, 1 <= n;
            let r = idx / n;
            let c = idx % n;
            let mut d = 0;
            while d < 8
                invariant
                    m == mat.len(),
                    n == mat[0].len(),
                    total == m * n,
                    1 <= m <= 6,
                    1 <= n <= 6,
                    total <= 36,
                    0 <= idx < total,
                    r == idx / n,
                    c == idx % n,
                    r < m,
                    c < n,
                    0 <= d <= 8,
                    forall|i: int| 0 <= i < mat.len() ==> 1 <= #[trigger] mat[i].len() <= 6,
                    forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() == mat[0].len(),
                    forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[0].len() ==> 1 <= #[trigger] mat[i][j] <= 9,
                    nums@ == Self::all_numbers_upto(mat@, idx as int) + Self::cell_numbers_upto(mat@, r as int, c as int, d as int),
                    forall|k: int| 0 <= k < nums.len() ==> 11 <= #[trigger] nums[k] <= 999_999,
                    nums.len() as int <= idx as int * 40 + d as int * 5,
                decreases 8 - d,
            {
                assert(mat[r as int].len() == n);
                let mut rr = r as i32;
                let mut cc = c as i32;
                let mut cur = mat[r][c];
                let mut active = true;
                let mut step = 1;
                proof {
                    assert(Self::row_at(r as int, d as int, 0) == r as int);
                    assert(Self::col_at(c as int, d as int, 0) == c as int);
                    assert(Self::in_bounds(mat@, r as int, c as int));
                    assert(Self::path_valid(mat@, r as int, c as int, d as int, 0));
                    Self::lemma_max_path_num_positive(0);
                }
                while step <= 5
                    invariant
                        m == mat.len(),
                        n == mat[0].len(),
                        total == m * n,
                        1 <= m <= 6,
                        1 <= n <= 6,
                        total <= 36,
                        0 <= idx < total,
                        r == idx / n,
                        c == idx % n,
                        r < m,
                        c < n,
                        0 <= d < 8,
                        1 <= step <= 6,
                        rr as int >= r as int - (step as int - 1),
                        rr as int <= r as int + (step as int - 1),
                        cc as int >= c as int - (step as int - 1),
                        cc as int <= c as int + (step as int - 1),
                        active ==> 1 <= cur,
                        active ==> cur as int <= Self::max_path_num(step as int - 1),
                        forall|i: int| 0 <= i < mat.len() ==> 1 <= #[trigger] mat[i].len() <= 6,
                        forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() == mat[0].len(),
                        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[0].len() ==> 1 <= #[trigger] mat[i][j] <= 9,
                        nums@ == Self::all_numbers_upto(mat@, idx as int) +
                                Self::cell_numbers_upto(mat@, r as int, c as int, d as int) +
                                Self::direction_numbers_upto(mat@, r as int, c as int, d as int, step as int - 1),
                        active ==> Self::path_valid(mat@, r as int, c as int, d as int, step as int - 1),
                        active ==> rr as int == Self::row_at(r as int, d as int, step as int - 1),
                        active ==> cc as int == Self::col_at(c as int, d as int, step as int - 1),
                        active ==> cur as int == Self::number_on_path(mat@, r as int, c as int, d as int, step as int - 1),
                        !active ==> !Self::path_valid(mat@, r as int, c as int, d as int, step as int - 1),
                        forall|k: int| 0 <= k < nums.len() ==> 11 <= #[trigger] nums[k] <= 999_999,
                        nums.len() as int <= idx as int * 40 + d as int * 5 + step as int - 1,
                    decreases 6 - step,
                {
                    let dx_d = Self::get_dx(d);
                    let dy_d = Self::get_dy(d);
                    rr += dx_d;
                    cc += dy_d;
                    if active && 0 <= rr && rr < m as i32 && 0 <= cc && cc < n as i32 {
                        assert(mat[rr as int].len() == n);
                        proof {
                            Self::lemma_max_path_num_bound(step as int - 1);
                            assert(cur as int <= Self::max_path_num(step as int - 1));
                            assert(Self::max_path_num(step as int - 1) <= 999_999);
                            assert(cur as int * 10 + 9 <= 999_999 * 10 + 9);
                        }
                        cur = cur * 10 + mat[rr as usize][cc as usize];
                        proof {
                            assert(active);
                            assert(Self::path_valid(mat@, r as int, c as int, d as int, step as int - 1));
                            assert(Self::row_at(r as int, d as int, step as int) == Self::row_at(r as int, d as int, step as int - 1) + Self::row_delta(d as int)) by {
                                let x = Self::row_delta(d as int);
                                assert(step as int * x == (step as int - 1) * x + x) by(nonlinear_arith);
                            };
                            assert(Self::col_at(c as int, d as int, step as int) == Self::col_at(c as int, d as int, step as int - 1) + Self::col_delta(d as int)) by {
                                let x = Self::col_delta(d as int);
                                assert(step as int * x == (step as int - 1) * x + x) by(nonlinear_arith);
                            };
                            assert(dx_d as int == Self::row_delta(d as int));
                            assert(dy_d as int == Self::col_delta(d as int));
                            assert(rr as int == Self::row_at(r as int, d as int, step as int));
                            assert(cc as int == Self::col_at(c as int, d as int, step as int));
                            assert(Self::in_bounds(mat@, rr as int, cc as int));
                            assert(Self::path_valid(mat@, r as int, c as int, d as int, step as int));
                            assert(cur as int == Self::number_on_path(mat@, r as int, c as int, d as int, step as int));
                        }
                        nums.push(cur);
                        proof {
                            assert(cur >= 11);
                            Self::lemma_max_path_num_bound(step as int);
                        }
                    } else {
                        proof {
                            if active {
                                assert(Self::row_at(r as int, d as int, step as int) == Self::row_at(r as int, d as int, step as int - 1) + Self::row_delta(d as int)) by {
                                    let x = Self::row_delta(d as int);
                                    assert(step as int * x == (step as int - 1) * x + x) by(nonlinear_arith);
                                };
                                assert(Self::col_at(c as int, d as int, step as int) == Self::col_at(c as int, d as int, step as int - 1) + Self::col_delta(d as int)) by {
                                    let x = Self::col_delta(d as int);
                                    assert(step as int * x == (step as int - 1) * x + x) by(nonlinear_arith);
                                };
                                assert(rr as int == Self::row_at(r as int, d as int, step as int));
                                assert(cc as int == Self::col_at(c as int, d as int, step as int));
                                assert(!Self::in_bounds(mat@, rr as int, cc as int));
                                assert(!Self::path_valid(mat@, r as int, c as int, d as int, step as int));
                            } else {
                                assert(!Self::path_valid(mat@, r as int, c as int, d as int, step as int - 1));
                                assert(!Self::path_valid(mat@, r as int, c as int, d as int, step as int));
                            }
                        }
                        active = false;
                    }
                    proof {
                        if Self::path_valid(mat@, r as int, c as int, d as int, step as int) {
                            assert(Self::direction_numbers_upto(mat@, r as int, c as int, d as int, step as int) ==
                                   Self::direction_numbers_upto(mat@, r as int, c as int, d as int, step as int - 1).push(
                                       Self::number_on_path(mat@, r as int, c as int, d as int, step as int) as i32));
                        } else {
                            assert(Self::direction_numbers_upto(mat@, r as int, c as int, d as int, step as int) ==
                                   Self::direction_numbers_upto(mat@, r as int, c as int, d as int, step as int - 1));
                        }
                    }
                    step += 1;
                }
                proof {
                    assert(step == 6);
                    assert(Self::direction_numbers_upto(mat@, r as int, c as int, d as int, 5) ==
                           Self::direction_numbers_upto(mat@, r as int, c as int, d as int, step as int - 1));
                }
                d += 1;
            }
            proof {
                assert(d == 8);
                assert(Self::cell_numbers_upto(mat@, r as int, c as int, 8) == Self::cell_numbers_upto(mat@, r as int, c as int, d as int));
                assert(nums.len() as int <= idx as int * 40 + 40) by(nonlinear_arith)
                    requires nums.len() as int <= idx as int * 40 + d as int * 5, d == 8usize;
            }
            idx += 1;
            proof {
                assert(nums.len() as int <= (idx as int) * 40) by(nonlinear_arith)
                    requires nums.len() as int <= (idx as int - 1) * 40 + 40;
            }
        }

        proof {
            assert(idx == total);
            assert(total as int == mat@.len() * mat@[0].len());
            assert(nums@ == Self::all_numbers_upto(mat@, total as int));
            assert(Self::all_numbers(mat@) == Self::all_numbers_upto(mat@, total as int));
            assert(nums.len() as int <= total as int * 40) by(nonlinear_arith)
                requires nums.len() as int <= idx as int * 40, idx == total;
            assert(total as int * 40 <= 1440) by(nonlinear_arith)
                requires total as int <= 36;
        }

        let mut best = -1;
        let mut best_count: i32 = 0;
        let mut i = 0;
        while i < nums.len()
            invariant
                nums@ == Self::all_numbers(mat@),
                0 <= i <= nums.len(),
                best_count >= 0,
                (best == -1) <==> (best_count == 0),
                best != -1 ==> Self::is_candidate_prime(best as int),
                best != -1 ==> best_count == Self::count_occurrences(nums@, best),
                best != -1 ==> 11 <= best <= 999_999,
                best == -1 ==> forall|k: int| 0 <= k < i ==> !Self::is_candidate_prime(#[trigger] nums[k] as int),
                forall|k: int| 0 <= k < i && Self::is_candidate_prime(#[trigger] nums[k] as int) ==>
                    (Self::count_occurrences(nums@, nums[k]) < best_count ||
                     (Self::count_occurrences(nums@, nums[k]) == best_count && nums[k] <= best)),
                forall|k: int| 0 <= k < nums.len() ==> 11 <= #[trigger] nums[k] <= 999_999,
                nums.len() <= 1440,
            decreases nums.len() - i,
        {
            let val = nums[i];
            if val > 10 && Self::is_prime(val) {
                let mut count: i32 = 0;
                let mut j = 0;
                while j < nums.len()
                    invariant
                        nums@ == Self::all_numbers(mat@),
                        0 <= j <= nums.len(),
                        nums.len() <= 1440,
                        val == nums[i as int],
                        count == Self::count_occurrences(nums@.subrange(0, j as int), val),
                        0 <= count <= j,
                        j > i ==> count >= 1,
                        forall|k: int| 0 <= k < nums.len() ==> 11 <= #[trigger] nums[k] <= 999_999,
                    decreases nums.len() - j,
                {
                    if nums[j] == val {
                        count += 1;
                    }
                    proof {
                        let old_j = j;
                        let prefix = nums@.subrange(0, old_j as int);
                        let next_prefix = nums@.subrange(0, (old_j + 1) as int);
                        assert(next_prefix =~= prefix.push(nums[old_j as int]));
                        Self::lemma_count_extend(prefix, val, nums[old_j as int]);
                    }
                    j += 1;
                }
                proof {
                    assert(nums@.subrange(0, nums.len() as int) =~= nums@);
                    assert(count >= 1);
                }

                if count > best_count || (count == best_count && val > best) {
                    best_count = count;
                    best = val;
                }
            }
            i += 1;
        }

        best
    }
}

}