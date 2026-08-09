use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_sums(mat: Seq<Vec<i32>>, row: int, col: int, remaining: int) -> nat
    decreases mat.len() - row, (if 0 <= row < mat.len() as int { mat[row].len() - col } else { 0 })
{
    if row >= mat.len() as int {
        if remaining >= 0 { 1 } else { 0 }
    } else if row < 0 || col >= mat[row].len() as int {
        0
    } else {
        count_sums(mat, row + 1, 0, remaining - mat[row][col] as int) +
        count_sums(mat, row, col + 1, remaining)
    }
}

pub open spec fn total_combos(mat: Seq<Vec<i32>>, row: int) -> int
    decreases mat.len() - row
{
    if row >= mat.len() as int { 1 }
    else { mat[row].len() as int * total_combos(mat, row + 1) }
}

pub open spec fn min_spec(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn sorted_asc(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

pub open spec fn merge_seq(a: Seq<int>, b: Seq<int>) -> Seq<int>
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        b
    } else if b.len() == 0 {
        a
    } else if a[0] <= b[0] {
        seq![a[0]] + merge_seq(a.drop_first(), b)
    } else {
        seq![b[0]] + merge_seq(a, b.drop_first())
    }
}

pub open spec fn all_between(s: Seq<int>, lo: int, hi: int) -> bool {
    forall|i: int| 0 <= i < s.len() ==> lo <= #[trigger] s[i] <= hi
}

pub open spec fn merge_capped(a: Seq<int>, b: Seq<int>, cap: int) -> Seq<int> {
    merge_seq(a, b).take(min_spec(cap, merge_seq(a, b).len() as int))
}

pub open spec fn shift_seq(s: Seq<int>, shift: int) -> Seq<int> {
    s.map_values(|e: int| shift + e)
}

pub open spec fn fold_cols(mat: Seq<Vec<i32>>, row: int, col: int, tail: Seq<int>, cap: int) -> Seq<int>
    decreases (if 0 <= row < mat.len() && col <= mat[row].len() { mat[row].len() - col } else { 0 }),
{
    if !(0 <= row < mat.len()) || col >= mat[row].len() {
        Seq::<int>::empty()
    } else {
        merge_capped(shift_seq(tail, mat[row][col] as int), fold_cols(mat, row, col + 1, tail, cap), cap)
    }
}

pub open spec fn capped_sums(mat: Seq<Vec<i32>>, row: int, cap: int) -> Seq<int>
    decreases mat.len() - row,
{
    if row >= mat.len() {
        seq![0int].take(min_spec(cap, 1))
    } else {
        fold_cols(mat, row, 0, capped_sums(mat, row + 1, cap), cap)
    }
}

pub open spec fn to_int_seq(s: Seq<i32>) -> Seq<int> {
    s.map_values(|x: i32| x as int)
}

fn merge_capped_exec(a: &Vec<i32>, b: &Vec<i32>, cap: usize) -> (result: Vec<i32>)
    requires
        sorted_asc(to_int_seq(a@)),
        sorted_asc(to_int_seq(b@)),
        a.len() <= 1000,
        b.len() <= 1000,
    ensures
        to_int_seq(result@) == merge_capped(to_int_seq(a@), to_int_seq(b@), cap as int),
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while result.len() < cap && (i < a.len() || j < b.len())
    {
        if j >= b.len() || (i < a.len() && a[i] <= b[j]) {
            result.push(a[i]);
            i += 1;
        } else {
            result.push(b[j]);
            j += 1;
        }
    }
    result
}

fn shift_exec(s: &Vec<i32>, shift: i32) -> (result: Vec<i32>)
    requires
        all_between(to_int_seq(s@), 0, 1_000_000),
        0 <= shift <= 5000,
    ensures
        to_int_seq(result@) == shift_seq(to_int_seq(s@), shift as int),
{
    let mut result: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < s.len()
    {
        result.push(s[idx] + shift);
        idx += 1;
    }
    result
}

fn fold_cols_exec(mat: &Vec<Vec<i32>>, row: usize, tail: &Vec<i32>, cap: usize) -> (result: Vec<i32>)
    requires
        row < mat.len(),
        mat.len() <= 40,
        cap <= 200,
        forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() >= 1 && mat[i].len() <= 40,
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
            1 <= #[trigger] mat[i][j] <= 5000,
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
            #[trigger] mat[i][j] <= mat[i][j + 1],
        to_int_seq(tail@) == capped_sums(mat@, row as int + 1, cap as int),
    ensures
        to_int_seq(result@) == fold_cols(mat@, row as int, 0, to_int_seq(tail@), cap as int),
{
    let n = mat[row].len();
    let mut acc: Vec<i32> = Vec::new();
    let mut c: usize = n;
    while c > 0
    {
        c -= 1;
        let shifted = shift_exec(tail, mat[row][c]);
        acc = merge_capped_exec(&shifted, &acc, cap);
    }
    acc
}

fn capped_sums_exec(mat: &Vec<Vec<i32>>, cap: usize) -> (result: Vec<i32>)
    requires
        1 <= mat.len() <= 40,
        cap <= 200,
        forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() >= 1 && mat[i].len() <= 40,
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
            1 <= #[trigger] mat[i][j] <= 5000,
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
            #[trigger] mat[i][j] <= mat[i][j + 1],
    ensures
        to_int_seq(result@) == capped_sums(mat@, 0, cap as int),
{
    let mut tail: Vec<i32> = Vec::new();
    if cap >= 1 {
        tail.push(0);
    }
    let m = mat.len();
    let mut row: usize = m;
    while row > 0
    {
        row -= 1;
        tail = fold_cols_exec(mat, row, &tail, cap);
    }
    tail
}

impl Solution {
    pub fn kth_smallest(mat: Vec<Vec<i32>>, k: i32) -> (result: i32)
        requires
            1 <= mat.len() <= 40,
            forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() >= 1 && mat[i].len() <= 40,
            forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() == mat[0].len(),
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
                1 <= #[trigger] mat[i][j] <= 5000,
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
                #[trigger] mat[i][j] <= mat[i][j + 1],
            1 <= k <= 200,
            k as int <= total_combos(mat@, 0),
        ensures
            count_sums(mat@, 0, 0, result as int) >= k as int,
            count_sums(mat@, 0, 0, result as int - 1) < k as int,
    {
        let l = capped_sums_exec(&mat, k as usize);
        let ans = l[(k - 1) as usize];
        ans
    }
}

}
