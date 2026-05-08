use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn is_co_growing(x: Seq<u32>, y: Seq<u32>, n: usize) -> bool {
    x.len() == n && y.len() == n &&
    forall|i: int| 0 <= i && i < n as int - 1 ==>
        (x[i] ^ y[i]) & (x[i + 1] ^ y[i + 1]) == (x[i] ^ y[i])
}

pub open spec fn lex_le_u32(a: Seq<u32>, b: Seq<u32>) -> bool {
    a.len() == b.len() && (
        a =~= b || exists|p: int|
            0 <= p < a.len()
            && a[p] < b[p]
            && forall|k: int| 0 <= k < p ==> a[k] == b[k]
    )
}

pub open spec fn y_valid(x: Seq<u32>, y: Seq<u32>, n: usize) -> bool {
    y.len() == n
    && (forall|i: int| 0 <= i < n as int ==> (y[i] as int) < 1073741824)
    && is_co_growing(x, y, n)
}

pub struct Solution;

impl Solution {
    pub fn co_growing(n: usize, x: Vec<u32>) -> (y: Vec<u32>)
        requires
            1 <= n && n <= 200000,
            x.len() == n,
            forall|i: int| 0 <= i && i < n ==> x@[i] < 1073741824,
        ensures
            y.len() == n,
            y_valid(x@, y@, n),
            forall|alt: Seq<u32>| y_valid(x@, alt, n) ==> lex_le_u32(y@, alt),
    {
        let mut y: Vec<u32> = Vec::new();
        let mut z: u32 = x[0];
        let y0 = z ^ x[0];
        y.push(y0);
        let mut i: usize = 1;
        while i < n {
            let old_z = z;
            z = z | x[i];
            let yi = z ^ x[i];
            y.push(yi);
            i += 1;
        }
        y
    }
}

}
