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

    proof fn lemma_injective_surjective(perm: Seq<int>, n: int, target: int)
        requires
            perm.len() == n,
            forall |i: int| 0 <= i < n ==> 0 <= #[trigger] perm[i] < n,
            forall |i: int, j: int| 0 <= i < j < n ==> perm[i] != perm[j],
            0 <= target < n,
        ensures
            exists |i: int| 0 <= i < n && perm[i] == target,
        decreases n
    {
        let p = perm[n - 1];
        if target == p {
            assert(perm[n - 1] == target);
            return;
        }
        let sub = Seq::new((n - 1) as nat, |i: int|
            if perm[i] < p { perm[i] } else { (perm[i] - 1) as int }
        );
        assert forall |i: int| 0 <= i < n - 1
            implies 0 <= #[trigger] sub[i] < n - 1
        by {
            if perm[i] < p {
            } else {
                assert(perm[i] != perm[n - 1]);
            }
        };
        assert forall |i: int, j: int| 0 <= i < j < n - 1
            implies sub[i] != sub[j]
        by {
            assert(perm[i] != perm[j]);
            if perm[i] < p && perm[j] < p {
            } else if perm[i] >= p && perm[j] >= p {
                assert(perm[i] != perm[n - 1]);
                assert(perm[j] != perm[n - 1]);
            } else if perm[i] < p && perm[j] >= p {
                assert(perm[j] != perm[n - 1]);
                assert(perm[j] > p);
                assert(sub[j] >= p);
                assert(sub[i] < p);
            } else {
                assert(perm[i] != perm[n - 1]);
                assert(perm[i] > p);
                assert(sub[i] >= p);
                assert(sub[j] < p);
            }
        };
        let v_prime: int = if target < p { target } else { target - 1 };
        Self::lemma_injective_surjective(sub, n - 1, v_prime);
        let i_sub: int = choose |i: int| 0 <= i < n - 1 && sub[i] == v_prime;
        if target < p {
            if perm[i_sub] < p {
                assert(perm[i_sub] == target);
            } else {
                assert(perm[i_sub] != perm[n - 1]);
                assert(perm[i_sub] > p);
                assert(perm[i_sub] - 1 == target);
                assert(target >= p);
                assert(false);
            }
        } else {
            if perm[i_sub] < p {
                assert(perm[i_sub] == v_prime);
                assert(v_prime >= p);
                assert(false);
            } else {
                assert(perm[i_sub] - 1 == v_prime);
                assert(perm[i_sub] == target);
            }
        }
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
        while i < m
            invariant
                0 <= i <= m,
                2 <= m <= 100,
                2 <= n <= 100,
                m == mat.len(),
                n == mat[0].len(),
                keys.len() == i,
                forall |r: int| 0 <= r < m as int ==> (#[trigger] mat[r]).len() == n,
                forall |r: int, c: int| 0 <= r < m as int && 0 <= c < n as int
                    ==> #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
                forall |idx: int| 0 <= idx < i as int
                    ==> #[trigger] keys@[idx] == Self::row_sum(mat[idx]@, n as int) * 200 + idx,
                forall |idx: int| 0 <= idx < i as int ==> 0 <= #[trigger] keys@[idx] <= 20099,
                forall |idx: int| 0 <= idx < i as int ==> keys@[idx] % 200 == idx,
            decreases m - i
        {
            let mut c: i32 = 0;
            let mut j: usize = 0;
            while j < n
                invariant
                    0 <= j <= n,
                    0 <= i < m,
                    2 <= n <= 100,
                    2 <= m <= 100,
                    n == mat[i as int].len(),
                    m == mat.len(),
                    forall |r: int, col: int| 0 <= r < m as int && 0 <= col < n as int
                        ==> #[trigger] mat[r][col] == 0 || mat[r][col] == 1,
                    0 <= c as int <= j as int,
                    c as int == Self::row_sum(mat[i as int]@, j as int),
                decreases n - j
            {
                proof {
                    assert(Self::row_sum(mat[i as int]@, (j + 1) as int)
                        == Self::row_sum(mat[i as int]@, j as int) + mat[i as int]@[j as int] as int);
                }
                c = c + mat[i][j];
                j = j + 1;
            }
            assert(c as int == Self::row_sum(mat[i as int]@, n as int));
            assert(0 <= c as int <= n as int);
            assert(0 <= c as int * 200 + i as int <= 20099) by(nonlinear_arith)
                requires
                    0 <= c as int <= 100,
                    0 <= i as int <= 99,
            {}
            proof {
                let key_val: int = c as int * 200 + i as int;
                assert(key_val % 200 == i as int) by(nonlinear_arith)
                    requires
                        0 <= c as int <= 100,
                        0 <= i as int <= 99,
                        key_val == c as int * 200 + i as int,
                {}
            }
            keys.push(c * 200 + i as i32);
            i = i + 1;
        }
        let ghost original_keys = keys@;
        proof {
            let r = Seq::new(original_keys.len(), |i: int| i);
            assert(Self::is_reorder_of(r, keys@, original_keys));
        }
        if m > 1 {
            let mut outer: usize = 1;
            while outer < m
                invariant
                    2 <= m <= 100,
                    m == mat.len(),
                    n == mat[0].len(),
                    keys.len() == m,
                    1 <= outer <= m,
                    forall |idx: int| 0 <= idx < m as int ==> 0 <= #[trigger] keys@[idx] <= 20099,
                    Self::sorted_between(keys@, 0, outer as int),
                    exists |r: Seq<int>| Self::is_reorder_of(r, keys@, original_keys),
                    forall |idx: int| 0 <= idx < m as int
                        ==> #[trigger] original_keys[idx] == Self::row_sum(mat[idx]@, n as int) * 200 + idx,
                    forall |idx: int| 0 <= idx < m as int ==> 0 <= #[trigger] original_keys[idx] <= 20099,
                    forall |idx: int| 0 <= idx < m as int ==> original_keys[idx] % 200 == idx,
                    original_keys.len() == m as int,
                    forall |r: int| 0 <= r < m as int ==> (#[trigger] mat[r]).len() == n,
                    forall |r: int, c: int| 0 <= r < m as int && 0 <= c < n as int
                        ==> #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
                decreases m - outer
            {
                let mut j: usize = outer;
                while j > 0
                    invariant
                        keys.len() == m,
                        2 <= m <= 100,
                        m == mat.len(),
                        n == mat[0].len(),
                        0 <= j <= outer < m,
                        forall |idx: int| 0 <= idx < m as int ==> 0 <= #[trigger] keys@[idx] <= 20099,
                        forall |x: int, y: int| 0 <= x <= y <= outer as int
                            ==> x != j as int && y != j as int ==> keys@[x] <= keys@[y],
                        Self::sorted_between(keys@, j as int, outer as int + 1),
                        exists |r: Seq<int>| Self::is_reorder_of(r, keys@, original_keys),
                        original_keys.len() == m as int,
                    decreases j
                {
                    if keys[j - 1] > keys[j] {
                        proof {
                            let r1 = choose |r: Seq<int>| Self::is_reorder_of(r, keys@, original_keys);
                            let r2 = r1.update(j as int - 1, r1[j as int]).update(j as int, r1[j as int - 1]);
                            assert(Self::is_reorder_of(r2,
                                keys@.update(j as int - 1, keys@[j as int]).update(j as int, keys@[j as int - 1]),
                                original_keys));
                        }
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

        proof {
            assert(Self::sorted_between(keys@, 0, m as int));

            let perm = choose |r: Seq<int>| Self::is_reorder_of(r, keys@, original_keys);

            assert forall |a: int, b: int| 0 <= a < b < m as int
                implies keys@[a] < keys@[b]
            by {
                assert(keys@[a] <= keys@[b]);
                if keys@[a] == keys@[b] {
                    assert(original_keys[perm[a]] % 200 == perm[a]);
                    assert(original_keys[perm[b]] % 200 == perm[b]);
                    assert(perm[a] == perm[b]);
                    assert(false);
                }
            };
        }

        let mut result: Vec<i32> = Vec::new();
        i = 0;
        while i < k as usize
            invariant
                0 <= i <= k as usize,
                1 <= k <= m as i32,
                2 <= m <= 100,
                m == mat.len(),
                n == mat[0].len(),
                keys.len() == m,
                result.len() == i,
                forall |idx: int| 0 <= idx < m as int ==> 0 <= #[trigger] keys@[idx] <= 20099,
                forall |a: int, b: int| 0 <= a < b < m as int ==> keys@[a] < keys@[b],
                forall |idx: int| 0 <= idx < i as int ==> #[trigger] result@[idx] == keys@[idx] % 200,
                exists |r: Seq<int>| Self::is_reorder_of(r, keys@, original_keys),
                forall |idx: int| 0 <= idx < m as int
                    ==> #[trigger] original_keys[idx] == Self::row_sum(mat[idx]@, n as int) * 200 + idx,
                forall |idx: int| 0 <= idx < m as int ==> 0 <= #[trigger] original_keys[idx] <= 20099,
                forall |idx: int| 0 <= idx < m as int ==> original_keys[idx] % 200 == idx,
                original_keys.len() == m as int,
                forall |r: int| 0 <= r < m as int ==> (#[trigger] mat[r]).len() == n,
                forall |r: int, c: int| 0 <= r < m as int && 0 <= c < n as int
                    ==> #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
            decreases k as usize - i
        {
            result.push(keys[i] % 200);
            i = i + 1;
        }

        proof {
            let perm = choose |r: Seq<int>| Self::is_reorder_of(r, keys@, original_keys);

            assert forall |i: int| 0 <= i < k as int
                implies 0 <= #[trigger] result@[i] < mat.len() as i32
            by {
                assert(result@[i] == keys@[i] % 200);
                assert(original_keys[perm[i]] % 200 == perm[i]);
                assert(0 <= perm[i] < m as int);
            };

            assert forall |i: int, j: int| 0 <= i < j < k as int
                implies result@[i] != result@[j]
            by {
                assert(result@[i] == keys@[i] % 200);
                assert(result@[j] == keys@[j] % 200);
                assert(keys@[i] < keys@[j]);
                if keys@[i] % 200 == keys@[j] % 200 {
                    assert(original_keys[perm[i]] % 200 == perm[i]);
                    assert(original_keys[perm[j]] % 200 == perm[j]);
                    assert(perm[i] == perm[j]);
                    assert(false);
                }
            };

            assert forall |i: int, j: int| 0 <= i < j < k as int
                implies Self::is_weaker(mat@, result@[i] as int, result@[j] as int)
            by {
                assert(result@[i] == keys@[i] % 200);
                assert(result@[j] == keys@[j] % 200);
                assert(keys@[i] < keys@[j]);

                let wi: int = perm[i];
                let wj: int = perm[j];
                assert(original_keys[wi] % 200 == wi);
                assert(original_keys[wj] % 200 == wj);
                assert(result@[i] as int == wi);
                assert(result@[j] as int == wj);

                let ci = Self::row_sum(mat[wi]@, n as int);
                let cj = Self::row_sum(mat[wj]@, n as int);
                assert(original_keys[wi] == ci * 200 + wi);
                assert(original_keys[wj] == cj * 200 + wj);
                assert(keys@[i] as int == ci * 200 + wi);
                assert(keys@[j] as int == cj * 200 + wj);

                assert(ci < cj || (ci == cj && wi < wj)) by(nonlinear_arith)
                    requires
                        ci * 200 + wi < cj * 200 + wj,
                        0 <= wi <= 99,
                        0 <= wj <= 99,
                        0 <= ci <= 100,
                        0 <= cj <= 100,
                {};

                assert(mat@[wi]@.len() == mat[wi]@.len());
                assert(mat[wi]@.len() == n);
                assert(Self::row_sum(mat@[wi]@, mat@[wi]@.len() as int) == ci);
                assert(mat@[wj]@.len() == mat[wj]@.len());
                assert(mat[wj]@.len() == n);
                assert(Self::row_sum(mat@[wj]@, mat@[wj]@.len() as int) == cj);
            };

            assert forall |p: int, r: int|
                0 <= p < k as int && 0 <= r < mat.len()
                && Self::is_weaker(mat@, r, result@[p] as int)
                implies (exists |q: int| 0 <= q < p && result@[q] == r as i32)
            by {
                assert(result@[p] == keys@[p] % 200);

                let wp: int = perm[p];
                assert(original_keys[wp] % 200 == wp);
                assert(result@[p] as int == wp);

                let count_r = Self::row_sum(mat[r]@, n as int);
                let count_p = Self::row_sum(mat[wp]@, n as int);

                assert(mat@[r]@.len() == mat[r]@.len());
                assert(mat[r]@.len() == n);
                assert(Self::row_sum(mat@[r]@, mat@[r]@.len() as int) == count_r);
                assert(mat@[wp]@.len() == mat[wp]@.len());
                assert(mat[wp]@.len() == n);
                assert(Self::row_sum(mat@[wp]@, mat@[wp]@.len() as int) == count_p);

                assert(Self::is_weaker(mat@, r, wp));
                assert(count_r < count_p || (count_r == count_p && r < wp));

                let key_r = original_keys[r];
                assert(key_r == count_r * 200 + r);
                assert(keys@[p] as int == count_p * 200 + wp);

                assert(key_r < keys@[p] as int) by(nonlinear_arith)
                    requires
                        count_r < count_p || (count_r == count_p && r < wp),
                        key_r == count_r * 200 + r,
                        keys@[p] as int == count_p * 200 + wp,
                        0 <= r <= 99,
                        0 <= wp <= 99,
                        0 <= count_r <= 100,
                        0 <= count_p <= 100,
                {};

                Self::lemma_injective_surjective(perm, m as int, r);
                let inv_r: int = choose |ii: int| 0 <= ii < m as int && perm[ii] == r;
                assert(keys@[inv_r] == original_keys[r]);
                assert(keys@[inv_r] as int == key_r);
                assert(keys@[inv_r] < keys@[p]);
                assert(inv_r < p) by {
                    if inv_r >= p {
                        if inv_r == p {
                            assert(keys@[inv_r] == keys@[p]);
                            assert(false);
                        } else {
                            assert(keys@[p] < keys@[inv_r]);
                            assert(false);
                        }
                    }
                };

                assert(inv_r < k as int);
                assert(result@[inv_r] == keys@[inv_r] % 200);
                assert(original_keys[r] % 200 == r);
                assert(keys@[inv_r] % 200 == r);
                assert(result@[inv_r] == r as i32);
            };
        }

        result
    }
}

}
