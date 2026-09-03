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
        (l <= x <= r && l <= y <= r && x != y && a[x - 1] != a[y - 1])
    }

    pub open spec fn spec_is_next_diff(a: Seq<i64>, i: int, v: int) -> bool
        recommends
            0 <= i < a.len(),
    {
        &&& i + 1 <= v <= a.len()
        &&& forall|u: int| i < u < v ==> #[trigger] a[u] == a[i]
        &&& v < a.len() ==> a[v] != a[i]
    }

    pub fn find_different_ones(a: Vec<i64>, queries: Vec<(usize, usize)>) -> (res: Vec<(i32, i32)>)
        requires
            2 <= a.len() <= 200000,
            forall|i: int| 0 <= i < a.len() as int ==> 1 <= #[trigger] a[i] <= 1000000,
            1 <= queries.len() && queries.len() <= 200000,
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

        proof {
            assert(nxt[n as int - 1] == n);
            assert(Self::spec_is_next_diff(a@, n as int - 1, n as int)) by {
                assert(n as int + 1 <= n as int + 1);
            }
        }

        let mut idx: usize = n - 1;
        while idx > 0
            invariant
                2 <= n <= 200000,
                n == a.len(),
                nxt.len() == n,
                0 <= idx <= n - 1,
                forall|j: int| 0 <= j < n as int ==> 1 <= #[trigger] a[j] <= 1000000,
                forall|i: int| idx as int <= i < n as int ==> Self::spec_is_next_diff(a@, i, #[trigger] nxt[i] as int),
            decreases idx,
        {
            let i = idx - 1;
            if a[i] != a[i + 1] {
                nxt[i] = i + 1;
                proof {
                    assert(Self::spec_is_next_diff(a@, i as int, i as int + 1));
                }
            } else {
                let v = nxt[i + 1];
                nxt[i] = v;
                proof {
                    assert(Self::spec_is_next_diff(a@, i as int + 1, v as int));
                    assert forall|u: int| (i as int) < u && u < (v as int) implies #[trigger] a[u] == a[i as int] by {
                        if u == i as int + 1 {
                        } else {
                            assert((i as int + 1) < u && u < (v as int));
                        }
                    };
                    assert(Self::spec_is_next_diff(a@, i as int, v as int));
                }
            }
            idx -= 1;
        }

        proof {
            assert forall|i: int| 0 <= i < n as int implies Self::spec_is_next_diff(a@, i, #[trigger] nxt[i] as int) by {
                assert(0 as int <= i);
            }
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
                forall|idx2: int| 0 <= idx2 < a.len() as int ==> 1 <= #[trigger] a[idx2] <= 1000000,
                forall|k2: int| 0 <= k2 < queries.len() as int ==> 1 <= #[trigger] queries[k2].0 < queries[k2].1 <= a.len(),
                forall|i: int| 0 <= i < n as int ==> Self::spec_is_next_diff(a@, i, #[trigger] nxt[i] as int),
                forall|k2: int| 0 <= k2 < qi as int ==> Self::valid_query_answer(a@, queries[k2], #[trigger] ans[k2]),
            decreases queries.len() - qi,
        {
            let l = queries[qi].0;
            let r = queries[qi].1;
            let li = l - 1;
            proof {
                assert(1 <= l < r <= a.len());
                assert(Self::spec_is_next_diff(a@, li as int, nxt[li as int] as int));
            }
            let j = nxt[li];
            if j < r {
                ans.push((l as i32, j as i32 + 1));
                proof {
                    assert(li as int + 1 <= j as int <= a.len() as int);
                    assert(a[j as int] != a[li as int]);
                    assert(Self::valid_query_answer(a@, queries[qi as int], ans[qi as int]));
                }
            } else {
                ans.push((-1, -1));
                proof {
                    assert forall|u0: int, v0: int| (li as int) <= u0 && u0 < v0 && v0 <= (r as int - 1)
                        implies a[u0] == a[v0] by {
                        if u0 == li as int {
                            assert((li as int) < v0 && v0 < (j as int));
                            assert(a[v0] == a[li as int]);
                        } else {
                            assert((li as int) < u0 && u0 < (j as int));
                            assert((li as int) < v0 && v0 < (j as int));
                            assert(a[u0] == a[li as int]);
                            assert(a[v0] == a[li as int]);
                        }
                    };
                    assert(Self::all_equal_range(a@, li as int, r as int - 1));
                    assert(Self::valid_query_answer(a@, queries[qi as int], ans[qi as int]));
                }
            }
            qi += 1;
        }
        ans
    }
}

}
