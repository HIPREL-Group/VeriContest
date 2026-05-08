use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn circular_sum(code: Seq<i32>, n: int, start: int, count: int) -> int
        decreases count,
    {
        if count <= 0 || n <= 0 {
            0
        } else {
            code[start % n] as int + Self::circular_sum(code, n, start + 1, count - 1)
        }
    }

    pub open spec fn decrypt_val(code: Seq<i32>, n: int, k: int, i: int) -> int {
        if k > 0 {
            Self::circular_sum(code, n, i + 1, k)
        } else if k < 0 {
            Self::circular_sum(code, n, i + n + k, -k)
        } else {
            0
        }
    }

    proof fn circular_sum_append(code: Seq<i32>, n: int, start: int, count: int)
        requires
            n > 0,
            count >= 0,
            code.len() == n,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] code[i] <= 100,
        ensures
            Self::circular_sum(code, n, start, count + 1) == Self::circular_sum(
                code,
                n,
                start,
                count,
            ) + code[(start + count) % n] as int,
        decreases count,
    {
        reveal_with_fuel(Solution::circular_sum, 2);
        if count > 0 {
            Self::circular_sum_append(code, n, start + 1, count - 1);
        }
    }

    proof fn circular_sum_slide(code: Seq<i32>, n: int, start: int, count: int)
        requires
            n > 0,
            count > 0,
            code.len() == n,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] code[i] <= 100,
        ensures
            Self::circular_sum(code, n, start + 1, count)
                == Self::circular_sum(code, n, start, count)
                    - code[start % n] as int
                    + code[(start + count) % n] as int,
    {
        Self::circular_sum_append(code, n, start + 1, count - 1);
    }

    proof fn circular_sum_bounds(code: Seq<i32>, n: int, start: int, count: int)
        requires
            n > 0,
            count >= 0,
            code.len() == n,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] code[i] <= 100,
        ensures
            count <= Self::circular_sum(code, n, start, count) <= count * 100,
        decreases count,
    {
        if count > 0 {
            Self::circular_sum_bounds(code, n, start + 1, count - 1);
        }
    }

    pub fn decrypt(code: Vec<i32>, k: i32) -> (result: Vec<i32>)
        requires
            1 <= code@.len() <= 100,
            forall|i: int| 0 <= i < code@.len() ==> 1 <= #[trigger] code@[i] <= 100,
            -(code@.len() as int - 1) <= k as int <= code@.len() as int - 1,
        ensures
            result@.len() == code@.len(),
            forall|i: int|
                0 <= i < code@.len() ==> (#[trigger] result@[i]) as int == Self::decrypt_val(
                    code@,
                    code@.len() as int,
                    k as int,
                    i,
                ),
    {
        let n = code.len();
        let mut result: Vec<i32> = Vec::new();
        if k == 0 {
            let mut i: usize = 0;
            while i < n
                invariant
                    n == code@.len(),
                    1 <= n <= 100,
                    k == 0,
                    0 <= i <= n,
                    result@.len() == i as int,
                    forall|idx: int|
                        0 <= idx < i as int ==> (#[trigger] result@[idx]) as int == 0,
                decreases n - i,
            {
                result.push(0);
                i = i + 1;
            }
            proof {
                assert forall|idx: int|
                    0 <= idx < code@.len() implies (#[trigger] result@[idx]) as int
                        == Self::decrypt_val(code@, n as int, k as int, idx)
                by {
                    assert(result@[idx] == 0i32);
                }
            }
            return result;
        }
        let mut sum: i32 = 0;
        if k > 0 {
            let mut j: usize = 0;
            while j < k as usize
                invariant
                    n == code@.len(),
                    1 <= n <= 100,
                    k > 0,
                    k as int <= n as int - 1,
                    0 <= j <= k as usize,
                    forall|m: int| 0 <= m < n as int ==> 1 <= #[trigger] code@[m] <= 100,
                    sum as int == Self::circular_sum(code@, n as int, 1, j as int),
                    j as int <= sum as int <= j as int * 100,
                decreases k as usize - j,
            {
                proof {
                    Self::circular_sum_append(code@, n as int, 1, j as int);
                }
                sum = sum + code[(1 + j) % n];
                j = j + 1;
            }
            proof {
                assert(sum as int == Self::circular_sum(code@, n as int, 1, k as int));
                assert(sum as int == Self::decrypt_val(code@, n as int, k as int, 0));
            }
            result.push(sum);
            let mut i: usize = 1;
            while i < n
                invariant
                    n == code@.len(),
                    1 <= n <= 100,
                    k > 0,
                    k as int <= n as int - 1,
                    1 <= i <= n,
                    forall|m: int| 0 <= m < n as int ==> 1 <= #[trigger] code@[m] <= 100,
                    result@.len() == i as int,
                    sum as int == Self::circular_sum(code@, n as int, i as int, k as int),
                    k as int <= sum as int <= k as int * 100,
                    forall|idx: int|
                        0 <= idx < i as int ==> (#[trigger] result@[idx]) as int
                            == Self::decrypt_val(code@, n as int, k as int, idx),
                decreases n - i,
            {
                proof {
                    Self::circular_sum_slide(code@, n as int, i as int, k as int);
                    Self::circular_sum_bounds(code@, n as int, (i + 1) as int, k as int);
                }
                sum = sum - code[i % n] + code[(i + k as usize) % n];
                proof {
                    assert(sum as int == Self::circular_sum(
                        code@,
                        n as int,
                        (i + 1) as int,
                        k as int,
                    ));
                    assert(sum as int == Self::decrypt_val(
                        code@,
                        n as int,
                        k as int,
                        i as int,
                    ));
                }
                result.push(sum);
                i = i + 1;
            }
        } else {
            let abs_k: usize = (-k) as usize;
            let mut j: usize = 0;
            while j < abs_k
                invariant
                    n == code@.len(),
                    1 <= n <= 100,
                    k < 0,
                    -(n as int - 1) <= k as int,
                    abs_k == (-k) as usize,
                    1 <= abs_k <= n - 1,
                    0 <= j <= abs_k,
                    forall|m: int| 0 <= m < n as int ==> 1 <= #[trigger] code@[m] <= 100,
                    sum as int == Self::circular_sum(
                        code@,
                        n as int,
                        (n - abs_k) as int,
                        j as int,
                    ),
                    j as int <= sum as int <= j as int * 100,
                decreases abs_k - j,
            {
                proof {
                    Self::circular_sum_append(
                        code@,
                        n as int,
                        (n - abs_k) as int,
                        j as int,
                    );
                }
                sum = sum + code[(n - abs_k + j) % n];
                j = j + 1;
            }
            proof {
                assert(abs_k as int == -(k as int));
                assert((n - abs_k) as int == 0int + n as int + k as int);
                assert(sum as int == Self::circular_sum(
                    code@,
                    n as int,
                    0int + n as int + k as int,
                    abs_k as int,
                ));
                assert(sum as int == Self::decrypt_val(code@, n as int, k as int, 0));
                assert(0int == 1int - 1 + 0);
            }
            result.push(sum);
            let mut i: usize = 1;
            while i < n
                invariant
                    n == code@.len(),
                    1 <= n <= 100,
                    k < 0,
                    -(n as int - 1) <= k as int,
                    abs_k == (-k) as usize,
                    1 <= abs_k <= n - 1,
                    1 <= i <= n,
                    forall|m: int| 0 <= m < n as int ==> 1 <= #[trigger] code@[m] <= 100,
                    result@.len() == i as int,
                    sum as int == Self::circular_sum(
                        code@,
                        n as int,
                        (i as int - 1 + n as int + k as int),
                        abs_k as int,
                    ),
                    abs_k as int <= sum as int <= abs_k as int * 100,
                    forall|idx: int|
                        0 <= idx < i as int ==> (#[trigger] result@[idx]) as int
                            == Self::decrypt_val(code@, n as int, k as int, idx),
                decreases n - i,
            {
                proof {
                    let prev_start = i as int - 1 + n as int + k as int;
                    Self::circular_sum_slide(
                        code@,
                        n as int,
                        prev_start,
                        abs_k as int,
                    );
                    Self::circular_sum_bounds(
                        code@,
                        n as int,
                        prev_start + 1,
                        abs_k as int,
                    );
                    assert(prev_start == i as int + n as int - abs_k as int - 1);
                    assert(prev_start + abs_k as int == i as int + n as int - 1);
                }
                sum = sum - code[(i + n - abs_k - 1) % n] + code[(i + n - 1) % n];
                proof {
                    let new_start = i as int + n as int + k as int;
                    assert(new_start == i as int - 1 + n as int + k as int + 1);
                    assert(sum as int == Self::circular_sum(
                        code@,
                        n as int,
                        new_start,
                        abs_k as int,
                    ));
                    assert(-(k as int) == abs_k as int);
                    assert(sum as int == Self::decrypt_val(
                        code@,
                        n as int,
                        k as int,
                        i as int,
                    ));
                }
                result.push(sum);
                i = i + 1;
            }
        }
        result
    }
}

}
