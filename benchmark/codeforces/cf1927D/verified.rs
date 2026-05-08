use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn all_equal_range(a: Seq<i64>, l: int, r: int) -> bool
        recommends
            0 <= l <= r < a.len(),
    {
        forall|i: int, j: int| l <= i && i < j && j <= r ==> a[i] == a[j]
    }

    pub open spec fn valid_query_answer(a: Seq<i64>, q: (usize, usize), out: (i32, i32)) -> bool {
        let l = q.0 as int;
        let r = q.1 as int;
        let x = out.0 as int;
        let y = out.1 as int;
        ((x == -1 && y == -1) && Self::all_equal_range(a, l - 1, r - 1))
        ||
        (l <= x < y <= r && a[x - 1] != a[y - 1])
    }

    pub fn find_different_ones(a: Vec<i64>, queries: Vec<(usize, usize)>) -> (res: Vec<(i32, i32)>)
        requires
            2 <= a.len() <= 200000,
            forall|i: int| 0 <= i < a.len() as int ==> 1 <= #[trigger] a[i] <= 1000000,
            forall|k: int| 0 <= k < queries.len() as int ==> 1 <= #[trigger] queries[k].0 < queries[k].1 <= a.len(),
        ensures
            res.len() == queries.len(),
            forall|k: int| 0 <= k < queries.len() as int ==> Self::valid_query_answer(a@, queries[k], #[trigger] res[k]),
    {
        let n = a.len();
        let mut nxt: Vec<usize> = Vec::with_capacity(n);
        let mut p: usize = 0;
        while p < n
            invariant
                n == a.len(),
                2 <= n <= 200000,
                0 <= p <= n,
                nxt.len() == p,
                forall|i: int| 0 <= i < nxt.len() as int ==> #[trigger] nxt[i] == n,
            decreases n - p,
        {
            nxt.push(n);
            p += 1;
        }
        let mut idx: usize = n - 1;
        while idx > 0
            invariant
                2 <= n <= 200000,
                n == a.len(),
                nxt.len() == n,
                0 <= idx <= n - 1,
                forall|j: int| 0 <= j < n as int ==> 1 <= #[trigger] a[j] <= 1000000,
            decreases idx,
        {
            let i = idx - 1;
            if a[i] != a[i + 1] {
                nxt[i] = i + 1;
            } else {
                nxt[i] = nxt[i + 1];
            }
            idx -= 1;
        }

        let mut ans: Vec<(i32, i32)> = Vec::with_capacity(queries.len());
        let mut qi: usize = 0;
        while qi < queries.len()
            invariant
                2 <= a.len() <= 200000,
                n == a.len(),
                nxt.len() == n,
                ans.len() == qi,
                0 <= qi <= queries.len(),
                forall|idx: int| 0 <= idx < a.len() as int ==> 1 <= #[trigger] a[idx] <= 1000000,
                forall|k2: int| 0 <= k2 < queries.len() as int ==> 1 <= #[trigger] queries[k2].0 < queries[k2].1 <= a.len(),
                forall|k2: int| 0 <= k2 < qi as int ==> Self::valid_query_answer(a@, queries[k2], #[trigger] ans[k2]),
            decreases queries.len() - qi,
        {
            let l = queries[qi].0;
            let r = queries[qi].1;
            let li = l - 1;
            let ri = r - 1;
            let mut found: bool = false;
            let mut pos: usize = li;
            let mut t: usize = li + 1;
            while t <= ri
                invariant
                    2 <= a.len() <= 200000,
                    1 <= l < r <= a.len(),
                    li + 1 <= t <= ri + 1,
                    li < ri < a.len(),
                    !found ==> forall|u: int| (li as int) < u && u < (t as int) ==> #[trigger] a[u] == a[li as int],
                    found ==> li < pos < t,
                    found ==> a[pos as int] != a[li as int],
                decreases ri + 1 - t,
            {
                if !found && a[t] != a[li] {
                    found = true;
                    pos = t;
                }
                t += 1;
            }
            let j = nxt[li];
            let j = if found { pos } else { r };
            if j < r {
                ans.push((l as i32, j as i32 + 1));
                proof {
                    assert(1 <= l < r <= a.len());
                    assert(found);
                    assert(li < pos <= ri);
                    assert(1 <= l <= r <= a.len());
                    assert(l as int <= l as int);
                    assert(j as int + 1 <= r as int);
                    assert(a[l as int - 1] != a[pos as int]);
                    assert(Self::valid_query_answer(a@, queries[qi as int], ans[qi as int]));
                }
            } else {
                ans.push((-1, -1));
                proof {
                    if !found {
                        assert(t == ri + 1);
                        assert forall|p0: int, q0: int| li as int <= p0 && p0 < q0 && q0 <= ri as int implies a[p0] == a[q0] by {
                            if p0 == li as int {
                                assert((li as int) < q0 && q0 < (t as int));
                                assert(a[q0] == a[li as int]);
                            } else {
                                assert((li as int) < p0 && p0 < (t as int));
                                assert((li as int) < q0 && q0 < (t as int));
                                assert(a[p0] == a[li as int]);
                                assert(a[q0] == a[li as int]);
                            }
                        };
                        assert(Self::all_equal_range(a@, li as int, ri as int));
                        assert(Self::valid_query_answer(a@, queries[qi as int], ans[qi as int]));
                    } else {
                        assert(false);
                    }
                }
            }
            qi += 1;
        }
        ans
    }
}

}
