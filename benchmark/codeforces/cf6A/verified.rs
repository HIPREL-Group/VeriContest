use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn triangle_inequality(a: int, b: int, c: int) -> bool {
    a + b > c && a + c > b && b + c > a
}

pub open spec fn valid_triple(i: int, j: int, k: int) -> bool {
    0 <= i < 4 && 0 <= j < 4 && 0 <= k < 4 && i != j && i != k && j != k
}

impl Solution {
    pub fn has_triangle(sticks: Vec<i32>) -> (res: bool)
        requires
            sticks.len() == 4,
            forall|i: int| 0 <= i < 4 ==> 1 <= #[trigger] sticks[i] as int <= 100,
        ensures
            res == exists|i: int, j: int, k: int|
                valid_triple(i, j, k)
                && triangle_inequality(sticks@[i] as int, sticks@[j] as int, sticks@[k] as int),
    {
        let mut found = false;
        let mut i = 0usize;
        while i < 4
            invariant
                sticks.len() == 4,
                forall|ii: int| 0 <= ii < 4 ==> 1 <= #[trigger] sticks[ii] as int <= 100,
                0 <= i <= 4,
                found == exists|ii: int, jj: int, kk: int|
                    (ii < i as int && valid_triple(ii, jj, kk) && triangle_inequality(sticks@[ii] as int, sticks@[jj] as int, sticks@[kk] as int)),
            decreases 4 - i,
        {
            let mut j = 0usize;
            while j < 4
                invariant
                    sticks.len() == 4,
                    forall|ii: int| 0 <= ii < 4 ==> 1 <= #[trigger] sticks[ii] as int <= 100,
                    i < 4,
                    0 <= j <= 4,
                    found == exists|ii: int, jj: int, kk: int|
                        ((ii < i as int && valid_triple(ii, jj, kk)) || (ii == i as int && jj < j as int && valid_triple(ii, jj, kk))) &&
                        triangle_inequality(sticks@[ii] as int, sticks@[jj] as int, sticks@[kk] as int),
                decreases 4 - j,
            {
                let mut k = 0usize;
                while k < 4
                    invariant
                        sticks.len() == 4,
                        forall|ii: int| 0 <= ii < 4 ==> 1 <= #[trigger] sticks[ii] as int <= 100,
                        i < 4,
                        j < 4,
                        0 <= k <= 4,
                        found == exists|ii: int, jj: int, kk: int|
                            ((ii < i as int && valid_triple(ii, jj, kk)) ||
                             (ii == i as int && jj < j as int && valid_triple(ii, jj, kk)) ||
                             (ii == i as int && jj == j as int && kk < k as int && valid_triple(ii, jj, kk))) &&
                            triangle_inequality(sticks@[ii] as int, sticks@[jj] as int, sticks@[kk] as int),
                    decreases 4 - k,
                {
                    if i != j && i != k && j != k {
                        let a = sticks[i] as i64;
                        let b = sticks[j] as i64;
                        let c = sticks[k] as i64;
                        if a + b > c && a + c > b && b + c > a {
                            proof {
                                assert(triangle_inequality(sticks@[i as int] as int, sticks@[j as int] as int, sticks@[k as int] as int));
                                assert(valid_triple(i as int, j as int, k as int));
                                assert(exists|ii: int, jj: int, kk: int|
                                    valid_triple(ii, jj, kk)
                                    && triangle_inequality(sticks@[ii] as int, sticks@[jj] as int, sticks@[kk] as int)) by {
                                    let ii = i as int;
                                    let jj = j as int;
                                    let kk = k as int;
                                }
                            }
                            found = true;
                        }
                    }
                    k += 1;
                }
                j += 1;
            }
            i += 1;
        }
        proof {
            assert forall|ii: int, jj: int, kk: int|
                valid_triple(ii, jj, kk) implies
                (ii < 4 && jj < 4 && kk < 4) by {
                    assert(0 <= ii < 4 && 0 <= jj < 4 && 0 <= kk < 4);
                }
            assert(i == 4);
            assert(found == exists|ii: int, jj: int, kk: int|
                (ii < 4 && valid_triple(ii, jj, kk) && triangle_inequality(sticks@[ii] as int, sticks@[jj] as int, sticks@[kk] as int)));
            assert(found == exists|ii: int, jj: int, kk: int|
                valid_triple(ii, jj, kk) && triangle_inequality(sticks@[ii] as int, sticks@[jj] as int, sticks@[kk] as int));
        }
        found
    }
}

}