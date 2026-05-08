use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn swapped_seq(s: Seq<i32>, i: int, j: int) -> Seq<i32> {
        s.update(i, s[j]).update(j, s[i])
    }

    pub open spec fn lex_le(a: Seq<i32>, b: Seq<i32>) -> bool {
        a.len() == b.len() && (
            a =~= b || exists|p: int|
                0 <= p < a.len()
                && a[p] < b[p]
                && forall|k: int| 0 <= k < p ==> a[k] == b[k]
        )
    }

    pub open spec fn sorted_range(s: Seq<i32>, lo: int, hi: int) -> bool {
        forall|m: int| lo <= m < hi ==> #[trigger] s[m] <= s[m + 1]
    }

    pub open spec fn skipped_range(s: Seq<i32>, lo: int, hi: int, pivot: i32) -> bool {
        forall|m: int| lo < m < hi ==> (#[trigger] s[m] >= pivot || s[m] == s[m - 1])
    }

    pub fn prev_perm_opt1(arr: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= arr@.len() <= 10_000,
            forall|i: int| 0 <= i < arr@.len() ==> 1 <= #[trigger] arr@[i] <= 10_000,
        ensures
            result@.len() == arr@.len(),
            (result@ =~= arr@) || (exists|i: int, j: int|
                0 <= i < j < arr@.len() as int
                && result@ =~= Self::swapped_seq(arr@, i, j)
                && arr@[i] > arr@[j]),
            Self::lex_le(result@, arr@),
            forall|p: int, q: int|
                0 <= p < q < arr@.len() as int && arr@[p] > arr@[q]
                ==> Self::lex_le(#[trigger] Self::swapped_seq(arr@, p, q), result@),
            (result@ =~= arr@) ==> Self::sorted_range(arr@, 0, arr@.len() as int - 1),
    {
        let n = arr.len();
        if n <= 1 {
            return arr;
        }
        let mut arr = arr;
        let mut k = n - 1;
        while k >= 1 && arr[k - 1] <= arr[k] {
            k -= 1;
        }
        if k == 0 && arr[0] <= arr[1] {
            return arr;
        }
        let idx = k - 1;
        let mut j = n - 1;
        while j > idx + 1 && (arr[j] >= arr[idx] || arr[j] == arr[j - 1]) {
            j -= 1;
        }
        let val_j = arr[j];
        let val_idx = arr[idx];
        arr.set(idx, val_j);
        arr.set(j, val_idx);
        arr
    }
}

}
