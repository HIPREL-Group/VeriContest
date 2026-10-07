use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_pair_sum(p: (i32, i32)) -> int {
    p.0 as int + p.1 as int
}

pub open spec fn spec_k(n: int) -> int {
    (3 * n + 3) / 2
}

pub open spec fn spec_value_in_pair(p: (i32, i32), v: int) -> bool {
    p.0 as int == v || p.1 as int == v
}

pub open spec fn spec_has_value_once(pairs: Seq<(i32, i32)>, n: int, v: int) -> bool {
    exists|i: int|
        0 <= i < n && #[trigger] spec_value_in_pair(pairs[i], v) && forall|j: int|
            0 <= j < n && j != i ==> !#[trigger] spec_value_in_pair(pairs[j], v)
}

pub open spec fn spec_is_valid_pairing(pairs: Seq<(i32, i32)>, n: int) -> bool {
    let base = spec_k(n);
    &&& n >= 1
    &&& n % 2 == 1
    &&& pairs.len() == n
    &&& forall|i: int| 0 <= i < n ==> {
        let s = spec_pair_sum(#[trigger] pairs[i]);
        base <= s <= base + n - 1
    }
    &&& forall|i: int, j: int|
        0 <= i < n && 0 <= j < n && i != j ==> spec_pair_sum(pairs[i]) != spec_pair_sum(pairs[j])
    &&& forall|v: int| 1 <= v <= 2 * n ==> #[trigger] spec_has_value_once(pairs, n, v)
}

impl Solution {
    pub fn matching_numbers(n: i32) -> (result: Option<Vec<(i32, i32)>>)
        requires
            1 <= n <= 100_000,
        ensures
            n % 2 == 0 ==> result == None::<Vec<(i32, i32)>>,
            n % 2 == 1 ==> result != None::<Vec<(i32, i32)>>
                && spec_is_valid_pairing(result->0@, n as int),
    {
        if n % 2 == 0 {
            return None;
        }
        let k: i32 = (3 * n + 3) / 2;
        let mut out: Vec<(i32, i32)> = Vec::new();
        let mut i: i32 = 1;
        while i <= (n + 1) / 2 {
            let a1: i32 = 2 * i - 1;
            let b1: i32 = k - i;
            out.push((a1, b1));
            i = i + 1;
        }
        let mut j: i32 = 1;
        while j <= (n - 1) / 2 {
            let a2: i32 = 2 * j;
            let b2: i32 = k + (n + 1) / 2 - j - 1;
            out.push((a2, b2));
            j = j + 1;
        }
        Some(out)
    }
}

}
