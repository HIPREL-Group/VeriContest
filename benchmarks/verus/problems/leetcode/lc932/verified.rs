use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn elem_pair(s: Seq<i32>, i: int, j: int) -> (i32, i32) {
        (s[i], s[j])
    }

    pub open spec fn in_range(x: int, n: i32) -> bool {
        1 <= x <= n
    }

    pub open spec fn triple(s: Seq<i32>, i: int, j: int, k: int) -> (i32, i32, i32) {
        (s[i], s[j], s[k])
    }

    pub open spec fn beautiful(s: Seq<i32>) -> bool {
        forall |i: int, j: int, k: int|
            0 <= i < k < j < s.len() ==>
            (#[trigger] Self::triple(s, i, j, k) == Self::triple(s, i, j, k))
            && 2 * s[k] != s[i] + s[j]
    }

    pub open spec fn count_le(s: Seq<i32>, bound: int, len: int) -> int
        decreases len,
    {
        if len <= 0 { 0 }
        else if (s[len - 1] as int) <= bound { 1 + Self::count_le(s, bound, len - 1) }
        else { Self::count_le(s, bound, len - 1) }
    }

    proof fn lemma_count_le_zero(s: Seq<i32>, len: int)
        requires
            0 <= len <= s.len(),
            forall |i: int| 0 <= i < len ==> (#[trigger] s[i] as int) >= 1,
        ensures Self::count_le(s, 0, len) == 0,
        decreases len,
    {
        if len > 0 { Self::lemma_count_le_zero(s, len - 1); }
    }

    proof fn lemma_count_le_skip(s: Seq<i32>, val: int, len: int)
        requires
            0 <= len <= s.len(),
            forall |i: int| 0 <= i < len ==> (#[trigger] s[i] as int) != val,
        ensures Self::count_le(s, val, len) == Self::count_le(s, val - 1, len),
        decreases len,
    {
        if len > 0 { Self::lemma_count_le_skip(s, val, len - 1); }
    }

    proof fn lemma_count_le_one(s: Seq<i32>, val: int, len: int)
        requires
            0 <= len <= s.len(),
            exists |j: int| 0 <= j < len && s[j] as int == val,
            forall |i: int, j: int| 0 <= i < j < len ==> s[i] != s[j],
        ensures Self::count_le(s, val, len) == Self::count_le(s, val - 1, len) + 1,
        decreases len,
    {
        if len <= 0 {
            assert(false);
        } else if s[len - 1] as int == val {
            assert forall |i: int| 0 <= i < len - 1 implies (#[trigger] s[i] as int) != val by {
                if s[i] as int == val {
                    assert(s[i] != s[len - 1]);
                }
            };
            Self::lemma_count_le_skip(s, val, len - 1);
        } else {
            let w = choose |j: int| 0 <= j < len && s[j] as int == val;
            assert(s[w] as int == val);
            assert(s[len - 1] as int != val);
            assert(w != len - 1);
            assert(0 <= w < len - 1);
            assert(exists |j: int| 0 <= j < len - 1 && s[j] as int == val);
            assert forall |i: int, j: int| 0 <= i < j < len - 1 implies s[i] != s[j] by {
                assert(s[i] != s[j]);
            };
            Self::lemma_count_le_one(s, val, len - 1);
        }
    }

    proof fn lemma_count_le_perm(s: Seq<i32>, nv: int, slen: int)
        requires
            0 <= nv <= slen,
            slen == s.len(),
            slen <= 2000,
            forall |i: int| 0 <= i < slen ==> (#[trigger] s[i] as int) >= 1,
            forall |i: int, j: int| 0 <= i < j < slen ==> s[i] != s[j],
            forall |x: int| #[trigger] Self::in_range(x, slen as i32) ==>
                exists |i: int| 0 <= i < slen && s[i] as int == x,
        ensures Self::count_le(s, nv, slen) == nv,
        decreases nv,
    {
        if nv == 0 {
            Self::lemma_count_le_zero(s, slen);
        } else {
            assert forall |i: int, j: int| 0 <= i < j < slen implies s[i] != s[j] by {
                assert(s[i] != s[j]);
            };
            Self::lemma_count_le_perm(s, nv - 1, slen);
            assert(Self::in_range(nv, slen as i32));
            assert forall |i: int, j: int| 0 <= i < j < slen implies s[i] != s[j] by {
                assert(s[i] != s[j]);
            };
            Self::lemma_count_le_one(s, nv, slen);
        }
    }

    proof fn lemma_perm_double(res: Seq<i32>, next: Seq<i32>)
        requires
            res.len() > 0,
            res.len() <= 1000,
            next.len() == 2 * res.len(),
            forall |j: int| 0 <= j < res.len() ==> next[j] == 2 * res[j] - 1,
            forall |j: int| 0 <= j < res.len() ==> next[res.len() + j] == 2 * res[j],
            forall |x: int| #[trigger] Self::in_range(x, res.len() as i32) ==>
                exists |i: int| 0 <= i < res.len() && res[i] as int == x,
        ensures
            forall |x: int| #[trigger] Self::in_range(x, next.len() as i32) ==>
                exists |i: int| 0 <= i < next.len() && next[i] as int == x,
    {
        assert forall |x: int| #[trigger] Self::in_range(x, next.len() as i32) implies
            exists |i: int| 0 <= i < next.len() && next[i] as int == x
        by {
            if Self::in_range(x, next.len() as i32) {
                if x % 2 == 1 {
                    let k = (x + 1) / 2;
                    assert(1 <= k <= res.len() as int);
                    assert(Self::in_range(k, res.len() as i32));
                    let j = choose |j: int| 0 <= j < res.len() && res[j] as int == k;
                    assert(next[j] == 2 * res[j] - 1);
                    assert((next[j] as int) == x);
                } else {
                    let k = x / 2;
                    assert(1 <= k <= res.len() as int);
                    assert(Self::in_range(k, res.len() as i32));
                    let j = choose |j: int| 0 <= j < res.len() && res[j] as int == k;
                    assert(next[res.len() + j] == 2 * res[j]);
                    assert((next[res.len() + j] as int) == x);
                }
            }
        }
    }

    proof fn lemma_beautiful_double(res: Seq<i32>, next: Seq<i32>)
        requires
            res.len() > 0,
            next.len() == 2 * res.len(),
            forall |j: int| 0 <= j < res.len() ==> next[j] == 2 * res[j] - 1,
            forall |j: int| 0 <= j < res.len() ==> next[res.len() + j] == 2 * res[j],
            Self::beautiful(res),
        ensures
            Self::beautiful(next),
    {
        assert forall |i: int, k: int, j: int| 0 <= i < k < j < res.len() implies
            2 * next[k] != next[i] + next[j]
        by {
            assert(#[trigger] Self::triple(res, i, j, k) == Self::triple(res, i, j, k));
            assert(2 * res[k] != res[i] + res[j]);
        };
        assert forall |i: int, k: int, j: int| res.len() <= i < k < j < next.len() implies
            2 * next[k] != next[i] + next[j]
        by {
            let ai = i - res.len();
            let ak = k - res.len();
            let aj = j - res.len();
            assert(0 <= ai < ak < aj < res.len());
            assert(#[trigger] Self::triple(res, ai, aj, ak) == Self::triple(res, ai, aj, ak));
            assert(2 * res[ak] != res[ai] + res[aj]);
        };
        assert forall |i: int, k: int, j: int|
            0 <= i < res.len() && res.len() <= k < j < next.len() implies
            2 * next[k] != next[i] + next[j]
        by {
            assert(next[i] == 2 * res[i] - 1);
            assert(next[k] == 2 * res[k - res.len()]);
            assert(next[j] == 2 * res[j - res.len()]);
            assert((next[i] as int) % 2 == 1);
            assert((next[k] as int) % 2 == 0);
            assert((next[j] as int) % 2 == 0);
            assert((2 * (next[k] as int)) % 2 == 0);
            assert(((next[i] as int) + (next[j] as int)) % 2 == 1);
        };
        assert forall |i: int, k: int, j: int|
            0 <= i < k < res.len() && res.len() <= j < next.len() implies
            2 * next[k] != next[i] + next[j]
        by {
            assert(next[i] == 2 * res[i] - 1);
            assert(next[k] == 2 * res[k] - 1);
            assert(next[j] == 2 * res[j - res.len()]);
            assert((next[i] as int) % 2 == 1);
            assert((next[k] as int) % 2 == 1);
            assert((next[j] as int) % 2 == 0);
            assert((2 * (next[k] as int)) % 2 == 0);
            assert(((next[i] as int) + (next[j] as int)) % 2 == 1);
        };
    }

    proof fn lemma_distinct_range_double(res: Seq<i32>, next: Seq<i32>)
        requires
            res.len() > 0,
            res.len() <= 1000,
            next.len() == 2 * res.len(),
            forall |j: int| 0 <= j < res.len() ==> next[j] == 2 * res[j] - 1,
            forall |j: int| 0 <= j < res.len() ==> next[res.len() + j] == 2 * res[j],
            forall |i: int| 0 <= i < res.len() ==> 1 <= #[trigger] res[i] <= res.len() as i32,
            forall |i: int, j: int| 0 <= i < j < res.len() ==>
                (#[trigger] Self::elem_pair(res, i, j) == Self::elem_pair(res, i, j)) && res[i] != res[j],
        ensures
            forall |i: int| 0 <= i < next.len() ==> 1 <= #[trigger] next[i] <= next.len() as i32,
            forall |i: int, j: int| 0 <= i < j < next.len() ==>
                (#[trigger] Self::elem_pair(next, i, j) == Self::elem_pair(next, i, j)) && next[i] != next[j],
    {
        assert forall |i: int| 0 <= i < next.len()
            implies 1 <= #[trigger] next[i] <= next.len() as i32
        by {
            if i < res.len() {
                assert(1 <= res[i] <= res.len() as i32);
                assert(next[i] == 2 * res[i] - 1);
                assert(1 <= next[i]);
                assert((next[i] as int) <= 2 * (res.len() as int) - 1);
            } else {
                let jj = i - res.len();
                assert(0 <= jj < res.len());
                assert(1 <= res[jj] <= res.len() as i32);
                assert(next[i] == 2 * res[jj]);
                assert(2 <= next[i]);
                assert((next[i] as int) <= 2 * (res.len() as int));
            }
        };
        assert forall |i: int, j: int| 0 <= i < j < next.len()
            implies (#[trigger] Self::elem_pair(next, i, j) == Self::elem_pair(next, i, j)) && next[i] != next[j]
        by {
            if j < res.len() {
                assert(Self::elem_pair(res, i, j) == Self::elem_pair(res, i, j));
                assert(res[i] != res[j]);
                assert(next[i] == 2 * res[i] - 1);
                assert(next[j] == 2 * res[j] - 1);
            } else if res.len() <= i {
                let ii = i - res.len();
                let jj = j - res.len();
                assert(0 <= ii < jj < res.len());
                assert(Self::elem_pair(res, ii, jj) == Self::elem_pair(res, ii, jj));
                assert(res[ii] != res[jj]);
                assert(next[i] == 2 * res[ii]);
                assert(next[j] == 2 * res[jj]);
            } else {
                let jj = j - res.len();
                assert(next[i] == 2 * res[i] - 1);
                assert(next[j] == 2 * res[jj]);
                assert((next[i] as int) % 2 == 1);
                assert((next[j] as int) % 2 == 0);
            }
        };
    }

    pub fn beautiful_array(n: i32) -> (result: Vec<i32>)
        requires
            1 <= n <= 1000,
        ensures
            result@.len() == n as int,
            forall |i: int| 0 <= i < result@.len() ==>
                1 <= #[trigger] result@[i] <= n,
            forall |i: int, j: int|
                0 <= i < j < result@.len() ==>
                #[trigger] Self::elem_pair(result@, i, j) == Self::elem_pair(result@, i, j)
                && result@[i] != result@[j],
            forall |x: int|
                #[trigger] Self::in_range(x, n) ==>
                exists |i: int| 0 <= i < result@.len() && result@[i] == x,
            forall |i: int, j: int, k: int|
                0 <= i < k < j < result@.len() ==>
                (#[trigger] Self::triple(result@, i, j, k) == Self::triple(result@, i, j, k))
                && 2 * result@[k] != result@[i] + result@[j],
    {
        let mut res = Vec::new();
        res.push(1);
        proof {
            assert(res@.len() == 1);
            assert(res@[0] == 1);
            assert(Self::beautiful(res@));
            assert forall |i: int| 0 <= i < res@.len() implies
                1 <= #[trigger] res@[i] <= res@.len() as i32 by {
                assert(i == 0);
            };
            assert forall |i: int, j: int| 0 <= i < j < res@.len() implies
                (#[trigger] Self::elem_pair(res@, i, j) == Self::elem_pair(res@, i, j))
                && res@[i] != res@[j] by {
                assert(false);
            };
            assert forall |x: int| #[trigger] Self::in_range(x, res@.len() as i32) implies
                exists |i: int| 0 <= i < res@.len() && res@[i] as int == x by {
                assert(x == 1);
                assert(exists |i: int| 0 <= i < res@.len() && res@[i] as int == x);
            };
        }
        while res.len() < n as usize
            invariant
                1 <= n <= 1000,
                res@.len() >= 1,
                res@.len() <= 2 * n as int,
                Self::beautiful(res@),
                forall |i: int| 0 <= i < res@.len() ==>
                    1 <= #[trigger] res@[i] <= res@.len() as i32,
                forall |i: int, j: int| 0 <= i < j < res@.len() ==>
                    (#[trigger] Self::elem_pair(res@, i, j) == Self::elem_pair(res@, i, j))
                    && res@[i] != res@[j],
                forall |x: int| #[trigger] Self::in_range(x, res@.len() as i32) ==>
                    exists |i: int| 0 <= i < res@.len() && res@[i] as int == x,
            decreases 2 * n as int - res@.len(),
        {
            let mut next = Vec::new();
            let mut i = 0usize;
            while i < res.len()
                invariant
                    1 <= n <= 1000,
                    res@.len() >= 1,
                    res@.len() < n as int,
                    i <= res.len(),
                    next@.len() == i as int,
                    forall |j: int| 0 <= j < next@.len() ==> next@[j] == 2 * res@[j] - 1,
                    forall |k: int| 0 <= k < res@.len() ==> 1 <= #[trigger] res@[k] <= res@.len() as i32,
                decreases res.len() - i,
            {
                proof {
                    assert(1 <= res@[i as int] <= res@.len() as i32);
                    assert((res@[i as int] as int) <= 1000);
                    assert(2 * (res@[i as int] as int) - 1 <= 1999);
                    assert(2 * (res@[i as int] as int) - 1 >= 1);
                }
                next.push(2 * res[i] - 1);
                i = i + 1;
            }
            let mut j = 0usize;
            while j < res.len()
                invariant
                    1 <= n <= 1000,
                    res@.len() >= 1,
                    res@.len() < n as int,
                    j <= res.len(),
                    next@.len() == res@.len() + j as int,
                    forall |p: int| 0 <= p < res@.len() ==> next@[p] == 2 * res@[p] - 1,
                    forall |p: int| 0 <= p < j as int ==> next@[res@.len() + p] == 2 * res@[p],
                    forall |k: int| 0 <= k < res@.len() ==> 1 <= #[trigger] res@[k] <= res@.len() as i32,
                decreases res.len() - j,
            {
                proof {
                    assert(1 <= res@[j as int] <= res@.len() as i32);
                    assert((res@[j as int] as int) <= 1000);
                    assert(2 * (res@[j as int] as int) <= 2000);
                }
                next.push(2 * res[j]);
                j = j + 1;
            }
            proof {
                assert(next@.len() == 2 * res@.len());
                assert forall |i: int, j: int| 0 <= i < j < res@.len() implies
                    (#[trigger] Self::elem_pair(res@, i, j) == Self::elem_pair(res@, i, j))
                    && res@[i] != res@[j] by {
                    assert(Self::elem_pair(res@, i, j) == Self::elem_pair(res@, i, j));
                    assert(res@[i] != res@[j]);
                };
                Self::lemma_beautiful_double(res@, next@);
                assert forall |i: int| 0 <= i < next@.len()
                    implies 1 <= #[trigger] next@[i] <= next@.len() as i32
                by {
                    if i < res@.len() {
                        assert(1 <= res@[i] <= res@.len() as i32);
                        assert(next@[i] == 2 * res@[i] - 1);
                        assert(1 <= next@[i]);
                        assert((next@[i] as int) <= 2 * res@.len() - 1);
                    } else {
                        let jj = i - res@.len();
                        assert(0 <= jj < res@.len());
                        assert(1 <= res@[jj] <= res@.len() as i32);
                        assert(next@[i] == 2 * res@[jj]);
                        assert(2 <= next@[i]);
                        assert((next@[i] as int) <= 2 * res@.len());
                    }
                };
                assert forall |i: int, j: int| 0 <= i < j < next@.len()
                    implies (#[trigger] Self::elem_pair(next@, i, j) == Self::elem_pair(next@, i, j))
                    && next@[i] != next@[j]
                by {
                    if j < res@.len() {
                        assert(Self::elem_pair(res@, i, j) == Self::elem_pair(res@, i, j));
                        assert(res@[i] != res@[j]);
                        assert(next@[i] == 2 * res@[i] - 1);
                        assert(next@[j] == 2 * res@[j] - 1);
                    } else if res@.len() <= i {
                        let ii = i - res@.len();
                        let jj = j - res@.len();
                        assert(0 <= ii < jj < res@.len());
                        assert(Self::elem_pair(res@, ii, jj) == Self::elem_pair(res@, ii, jj));
                        assert(res@[ii] != res@[jj]);
                        assert(next@[i] == 2 * res@[ii]);
                        assert(next@[j] == 2 * res@[jj]);
                    } else {
                        let jj = j - res@.len();
                        assert(next@[i] == 2 * res@[i] - 1);
                        assert(next@[j] == 2 * res@[jj]);
                        assert((next@[i] as int) % 2 == 1);
                        assert((next@[j] as int) % 2 == 0);
                    }
                };
                Self::lemma_perm_double(res@, next@);
            }
            res = next;
        }
        let ghost mut srcs: Seq<int> = Seq::empty();
        let mut out = Vec::new();
        let mut idx = 0usize;
        while idx < res.len()
            invariant
                1 <= n <= 1000,
                res@.len() >= n as int,
                res@.len() <= 2 * n as int,
                idx as int <= res@.len(),
                out@.len() == Self::count_le(res@, n as int, idx as int),
                srcs.len() == out@.len(),
                forall |i: int| 0 <= i < srcs.len() ==>
                    0 <= (#[trigger] srcs[i]) && srcs[i] < idx as int,
                forall |i: int| 0 <= i < srcs.len() ==>
                    out@[i] == res@[srcs[i]],
                forall |i: int, j: int| 0 <= i < j < srcs.len() ==>
                    (#[trigger] srcs[i]) < (#[trigger] srcs[j]),
                forall |i: int| 0 <= i < out@.len() ==>
                    1 <= #[trigger] out@[i] <= n,
                forall |j: int| 0 <= j < idx as int ==>
                    ((#[trigger] res@[j] as int) <= n as int ==>
                     exists |i: int| 0 <= i < out@.len() && out@[i] == res@[j]),
                Self::beautiful(res@),
                forall |i: int| 0 <= i < res@.len() ==>
                    1 <= #[trigger] res@[i] <= res@.len() as i32,
                forall |i: int, j: int| 0 <= i < j < res@.len() ==>
                    (#[trigger] Self::elem_pair(res@, i, j) == Self::elem_pair(res@, i, j))
                    && res@[i] != res@[j],
                forall |x: int| #[trigger] Self::in_range(x, res@.len() as i32) ==>
                    exists |i: int| 0 <= i < res@.len() && res@[i] as int == x,
            decreases res.len() - idx,
        {
            let ghost old_out = out@;
            let ghost old_idx = idx as int;
            proof {
                assert forall |j: int| 0 <= j < old_idx implies
                    (((#[trigger] res@[j] as int) <= n as int) ==>
                     exists |i: int| 0 <= i < old_out.len() && old_out[i] == res@[j]) by {
                    if (res@[j] as int) <= n as int {
                        let i = choose |i: int| 0 <= i < old_out.len() && old_out[i] == res@[j];
                        assert(0 <= i < old_out.len());
                        assert(old_out[i] == res@[j]);
                    }
                };
            }
            if res[idx] <= n {
                proof {
                    srcs = srcs.push(idx as int);
                }
                out.push(res[idx]);
                proof {
                    assert(out@[out@.len() - 1] == res@[old_idx]);
                    assert(exists |i: int| 0 <= i < out@.len() && out@[i] == res@[old_idx]);
                }
            }
            proof {
                assert forall |j: int| 0 <= j < old_idx + 1 implies
                    (((#[trigger] res@[j] as int) <= n as int) ==>
                     exists |i: int| 0 <= i < out@.len() && out@[i] == res@[j]) by {
                    if j < old_idx {
                        if (res@[j] as int) <= n as int {
                            let i = choose |i: int| 0 <= i < old_out.len() && old_out[i] == res@[j];
                            assert(0 <= i < out@.len());
                            assert(out@[i] == res@[j]);
                        }
                    } else {
                        assert(j == old_idx);
                        if (res@[j] as int) <= n as int {
                            assert(exists |i: int| 0 <= i < out@.len() && out@[i] == res@[j]);
                        }
                    }
                };
            }
            idx = idx + 1;
        }
        proof {
            assert forall |i: int, j: int| 0 <= i < j < res@.len() implies res@[i] != res@[j] by {
                assert(Self::elem_pair(res@, i, j) == Self::elem_pair(res@, i, j));
                assert(res@[i] != res@[j]);
            };
            Self::lemma_count_le_perm(res@, n as int, res@.len() as int);
            assert(out@.len() == n as int);

            assert forall |i: int, j: int| 0 <= i < j < out@.len() implies
                (#[trigger] Self::elem_pair(out@, i, j) == Self::elem_pair(out@, i, j))
                && out@[i] != out@[j]
            by {
                assert(out@[i] == res@[srcs[i]]);
                assert(out@[j] == res@[srcs[j]]);
                assert(srcs[i] < srcs[j]);
                assert(srcs[j] < res@.len());
                assert(Self::elem_pair(res@, srcs[i], srcs[j])
                    == Self::elem_pair(res@, srcs[i], srcs[j]));
                assert(res@[srcs[i]] != res@[srcs[j]]);
            };

            assert forall |x: int| #[trigger] Self::in_range(x, n) implies
                exists |i: int| 0 <= i < out@.len() && out@[i] == x
            by {
                assert(n as int <= res@.len() as int);
                assert(Self::in_range(x, res@.len() as i32));
                let jj = choose |jj: int| 0 <= jj < res@.len() && res@[jj] as int == x;
                assert(res@[jj] as int <= n as int);
                assert(0 <= jj < idx as int);
            };

            assert forall |i: int, k: int, j: int|
                0 <= i < k < j < out@.len() implies
                (#[trigger] Self::triple(out@, i, j, k) == Self::triple(out@, i, j, k))
                && 2 * out@[k] != out@[i] + out@[j]
            by {
                assert(out@[i] == res@[srcs[i]]);
                assert(out@[k] == res@[srcs[k]]);
                assert(out@[j] == res@[srcs[j]]);
                assert(srcs[i] < srcs[k]);
                assert(srcs[k] < srcs[j]);
                assert(srcs[j] < res@.len());
                assert(Self::triple(res@, srcs[i], srcs[j], srcs[k])
                    == Self::triple(res@, srcs[i], srcs[j], srcs[k]));
            };
        }
        out
    }
}

}
