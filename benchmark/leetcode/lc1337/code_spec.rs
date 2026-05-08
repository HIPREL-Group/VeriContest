use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn row_sum(row: Seq<i32>, len: int) -> int
        decreases len
    {
        if len <= 0 {
            0
        } else {
            Self::row_sum(row, len - 1) + row[len - 1] as int
        }
    }

    pub open spec fn is_weaker(mat: Seq<Vec<i32>>, i: int, j: int) -> bool {
        let ci = Self::row_sum(mat[i]@, mat[i]@.len() as int);
        let cj = Self::row_sum(mat[j]@, mat[j]@.len() as int);
        ci < cj || (ci == cj && i < j)
    }

    pub open spec fn sorted_between(a: Seq<i32>, from: int, to: int) -> bool {
        forall |i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
    }

    pub open spec fn is_reorder_of(r: Seq<int>, p: Seq<i32>, s: Seq<i32>) -> bool {
        &&& r.len() == s.len()
        &&& forall |i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
        &&& forall |i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
        &&& p =~= r.map_values(|i: int| s[i])
    }

    pub fn k_weakest_rows(mat: Vec<Vec<i32>>, k: i32) -> (result: Vec<i32>)
        requires
            2 <= mat.len() <= 100,
            forall |i: int| 0 <= i < mat.len() ==> 2 <= (#[trigger] mat[i]).len() <= 100,
            forall |i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() == mat[0].len(),
            1 <= k <= mat.len() as i32,
            forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len()
                ==> #[trigger] mat[i][j] == 0 || mat[i][j] == 1,
        ensures
            result.len() == k as int,
            forall |i: int| 0 <= i < k as int ==> 0 <= #[trigger] result@[i] < mat.len() as i32,
            forall |i: int, j: int| 0 <= i < j < k as int ==> result@[i] != result@[j],
            forall |i: int, j: int| 0 <= i < j < k as int
                ==> Self::is_weaker(mat@, result@[i] as int, result@[j] as int),
            forall |p: int, r: int| 0 <= p < k as int && 0 <= r < mat.len()
                && Self::is_weaker(mat@, r, result@[p] as int)
                ==> (exists |q: int| 0 <= q < p && result@[q] == r as i32),
    {
        let m = mat.len();
        let n = mat[0].len();
        let mut keys: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < m {
            let mut c: i32 = 0;
            let mut j: usize = 0;
            while j < n {
                c = c + mat[i][j];
                j = j + 1;
            }
            keys.push(c * 200 + i as i32);
            i = i + 1;
        }
        if m > 1 {
            let mut outer: usize = 1;
            while outer < m {
                let mut j: usize = outer;
                while j > 0 {
                    if keys[j - 1] > keys[j] {
                        let tmp1 = keys[j];
                        let tmp2 = keys[j - 1];
                        keys.set(j - 1, tmp1);
                        keys.set(j, tmp2);
                    }
                    j -= 1;
                }
                outer += 1;
            }
        }
        let mut result: Vec<i32> = Vec::new();
        i = 0;
        while i < k as usize {
            result.push(keys[i] % 200);
            i = i + 1;
        }
        result
    }
}

}
