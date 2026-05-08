use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn in_prefix(s: Seq<i32>, end: int, x: i32) -> bool {
        exists |j: int| 0 <= j < end && #[trigger] s[j] == x
    }

    pub open spec fn count_matches(a: Seq<i32>, b: Seq<i32>, end: int, idx: int) -> int
        recommends
            b.len() == a.len(),
            0 <= end <= a.len(),
            0 <= idx <= end,
        decreases idx,
    {
        if idx <= 0 {
            0
        } else {
            Self::count_matches(a, b, end, idx - 1)
                + if Self::in_prefix(b, end, a[idx - 1]) { 1int } else { 0int }
        }
    }

    pub open spec fn prefix_common_count(a: Seq<i32>, b: Seq<i32>, end: int) -> int
        recommends
            b.len() == a.len(),
            0 <= end <= a.len(),
    {
        Self::count_matches(a, b, end, end)
    }

    pub fn find_the_prefix_common_array(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= a.len() <= 50,
            b.len() == a.len(),
            forall |i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= a.len(),
            forall |i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= b.len(),
            forall |i: int, j: int| 0 <= i < j < a.len() ==> a[i] != a[j],
            forall |i: int, j: int| 0 <= i < j < b.len() ==> b[i] != b[j],
        ensures
            result.len() == a.len(),
            forall |i: int| 0 <= i < result.len() ==> {
                &&& 0 <= #[trigger] result[i] <= i + 1
                &&& result[i] as int == Self::prefix_common_count(a@, b@, i + 1)
            },
    {
        let n = a.len();
        let mut pos: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= n
            invariant
                n == a.len(),
                b.len() == n,
                1 <= n <= 50,
                0 <= k <= n + 1,
                pos.len() == k,
                forall |t: int| 0 <= t < pos.len() ==> #[trigger] pos[t] == -1,
            decreases n + 1 - k,
        {
            pos.push(-1);
            k = k + 1;
        }

        let mut i: usize = 0;
        while i < n
            invariant
                n == a.len(),
                b.len() == n,
                1 <= n <= 50,
                0 <= i <= n,
                pos.len() == n + 1,
                forall |idx: int| 0 <= idx < b.len() ==> 1 <= #[trigger] b[idx] <= b.len(),
                forall |p: int, q: int| 0 <= p < q < b.len() ==> b[p] != b[q],
                forall |j: int| 0 <= j < i ==> #[trigger] pos[b[j] as int] == j,
                forall |v: int| 1 <= v <= n ==> {
                    &&& #[trigger] pos[v] == -1 || 0 <= pos[v] < i
                    &&& pos[v] != -1 ==> b[pos[v] as int] == v as i32
                },
            decreases n - i,
        {
            let val = b[i];
            pos.set(val as usize, i as i32);
            proof {
                assert(1 <= val <= n);
                assert(pos[val as int] == i as i32);
                assert forall |j: int| 0 <= j < i + 1 implies #[trigger] pos[b[j] as int] == j by {
                    if j < i {
                        assert(b[j] != b[i as int]);
                        assert(pos[b[j] as int] == j);
                    } else {
                        assert(j == i as int);
                    }
                }
                assert forall |v: int| 1 <= v <= n implies {
                    &&& #[trigger] pos[v] == -1 || 0 <= pos[v] < i + 1
                    &&& pos[v] != -1 ==> b[pos[v] as int] == v as i32
                } by {
                    if v == val as int {
                        assert(pos[v] == i as i32);
                        assert(b[i as int] == v as i32);
                    } else {
                        assert(pos[v] == -1 || 0 <= pos[v] < i);
                        if pos[v] != -1 {
                            assert(b[pos[v] as int] == v as i32);
                        }
                    }
                }
            }
            i = i + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        i = 0;
        while i < n
            invariant
                n == a.len(),
                b.len() == n,
                1 <= n <= 50,
                0 <= i <= n,
                pos.len() == n + 1,
                forall |idx: int| 0 <= idx < a.len() ==> 1 <= #[trigger] a[idx] <= a.len(),
                forall |idx: int| 0 <= idx < b.len() ==> 1 <= #[trigger] b[idx] <= b.len(),
                forall |p: int, q: int| 0 <= p < q < a.len() ==> a[p] != a[q],
                forall |p: int, q: int| 0 <= p < q < b.len() ==> b[p] != b[q],
                forall |j: int| 0 <= j < n ==> #[trigger] pos[b[j] as int] == j,
                forall |v: int| 1 <= v <= n ==> {
                    &&& #[trigger] pos[v] == -1 || 0 <= pos[v] < n
                    &&& pos[v] != -1 ==> b[pos[v] as int] == v as i32
                },
                result.len() == i,
                forall |k: int| 0 <= k < result.len() ==> {
                    &&& 0 <= #[trigger] result[k] <= k + 1
                    &&& result[k] as int == Self::prefix_common_count(a@, b@, k + 1)
                },
            decreases n - i,
        {
            let mut common: i32 = 0;
            let mut p: usize = 0;
            while p <= i
                invariant
                    n == a.len(),
                    b.len() == n,
                    1 <= n <= 50,
                    0 <= i < n,
                    0 <= p <= i + 1,
                    pos.len() == n + 1,
                    forall |idx: int| 0 <= idx < a.len() ==> 1 <= #[trigger] a[idx] <= a.len(),
                    forall |idx: int| 0 <= idx < b.len() ==> 1 <= #[trigger] b[idx] <= b.len(),
                    forall |q: int, r: int| 0 <= q < r < b.len() ==> b[q] != b[r],
                    forall |j: int| 0 <= j < n ==> #[trigger] pos[b[j] as int] == j,
                    forall |v: int| 1 <= v <= n ==> {
                        &&& #[trigger] pos[v] == -1 || 0 <= pos[v] < n
                        &&& pos[v] != -1 ==> b[pos[v] as int] == v as i32
                    },
                    0 <= common <= p,
                    common as int == Self::count_matches(a@, b@, (i + 1) as int, p as int),
                decreases i + 1 - p,
            {
                let x = a[p];
                let idx = pos[x as usize];
                proof {
                    assert(1 <= x <= n);
                    assert(1 <= x as int <= n);
                    assert(pos[x as int] == -1 || 0 <= pos[x as int] < n) by {
                        assert(1 <= x as int <= n);
                    };
                    assert(idx == pos[x as int]);
                    assert(idx == -1 || 0 <= idx < n);
                    if idx != -1 {
                        assert(pos[x as int] != -1);
                        assert(b[pos[x as int] as int] == x as i32) by {
                            assert(1 <= x as int <= n);
                        };
                        assert(b[idx as int] == x);
                    }
                    assert((idx >= 0 && idx <= i as i32) ==> Self::in_prefix(b@, (i + 1) as int, x)) by {
                        if idx >= 0 && idx <= i as i32 {
                            assert(0 <= idx as int);
                            assert((idx as int) < (i + 1) as int);
                            assert(b[idx as int] == x);
                        }
                    }
                    assert((Self::in_prefix(b@, (i + 1) as int, x)) ==> (idx >= 0 && idx <= i as i32)) by {
                        if Self::in_prefix(b@, (i + 1) as int, x) {
                            let t = choose |t: int| 0 <= t < (i + 1) as int && b[t] == x;
                            assert(0 <= t < n);
                            assert(pos[b[t] as int] == t);
                            assert(pos[x as int] == t);
                            assert(idx as int == t);
                        }
                    }
                }

                if idx >= 0 && idx <= i as i32 {
                    common = common + 1;
                }
                proof {
                    assert(common as int == Self::count_matches(a@, b@, (i + 1) as int, (p + 1) as int)) by {
                        assert(Self::count_matches(a@, b@, (i + 1) as int, (p + 1) as int)
                            == Self::count_matches(a@, b@, (i + 1) as int, p as int)
                                + if Self::in_prefix(b@, (i + 1) as int, a[p as int]) { 1int } else { 0int });
                        if idx >= 0 && idx <= i as i32 {
                            assert(Self::in_prefix(b@, (i + 1) as int, a[p as int]));
                        } else {
                            assert(!Self::in_prefix(b@, (i + 1) as int, a[p as int]));
                        }
                    }
                }
                p = p + 1;
            }

            proof {
                assert(p == i + 1);
                assert(common as int == Self::prefix_common_count(a@, b@, (i + 1) as int));
            }
            let ghost old_result = result@;
            result.push(common);
            proof {
                assert(result@ == old_result.push(common));
                assert forall |kk: int| 0 <= kk < result.len() implies {
                    &&& 0 <= #[trigger] result[kk] <= kk + 1
                    &&& result[kk] as int == Self::prefix_common_count(a@, b@, kk + 1)
                } by {
                    if kk < old_result.len() {
                        assert(result@[kk] == old_result[kk]);
                    } else {
                        assert(kk == old_result.len());
                    }
                }
            }

            i = i + 1;
        }

        result
    }
}

}
