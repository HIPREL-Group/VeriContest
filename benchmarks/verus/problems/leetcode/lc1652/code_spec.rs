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
            while i < n {
                result.push(0);
                i = i + 1;
            }
            return result;
        }
        let mut sum: i32 = 0;
        if k > 0 {
            let mut j: usize = 0;
            while j < k as usize {
                sum = sum + code[(1 + j) % n];
                j = j + 1;
            }
            result.push(sum);
            let mut i: usize = 1;
            while i < n {
                sum = sum - code[i % n] + code[(i + k as usize) % n];
                result.push(sum);
                i = i + 1;
            }
        } else {
            let abs_k: usize = (-k) as usize;
            let mut j: usize = 0;
            while j < abs_k {
                sum = sum + code[(n - abs_k + j) % n];
                j = j + 1;
            }
            result.push(sum);
            let mut i: usize = 1;
            while i < n {
                sum = sum - code[(i + n - abs_k - 1) % n] + code[(i + n - 1) % n];
                result.push(sum);
                i = i + 1;
            }
        }
        result
    }
}

}
