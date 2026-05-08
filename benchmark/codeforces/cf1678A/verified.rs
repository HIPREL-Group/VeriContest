use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_prefix_count(s: Seq<i32>, i: int, v: int) -> int
    decreases i,
{
    if i <= 0 {
        0int
    } else {
        spec_prefix_count(s, i - 1, v) + if s[i - 1] as int == v {
            1int
        } else {
            0int
        }
    }
}

pub open spec fn spec_has_duplicate(s: Seq<i32>) -> bool {
    exists|vv: int|
        #![trigger spec_prefix_count(s, s.len() as int, vv)]
        0 <= vv && vv <= 100 && spec_prefix_count(s, s.len() as int, vv) >= 2
}

pub open spec fn spec_min_ops_answer(s: Seq<i32>) -> int {
    let n = s.len() as int;
    let z = spec_prefix_count(s, n, 0);
    if z > 0 {
        n - z
    } else if spec_has_duplicate(s) {
        n
    } else {
        n + 1
    }
}

proof fn lemma_spec_prefix_count_nonneg(s: Seq<i32>, i: int, v: int)
    requires
        0 <= i <= s.len(),
    ensures
        spec_prefix_count(s, i, v) >= 0,
    decreases i,
{
    if i <= 0 {
    } else {
        lemma_spec_prefix_count_nonneg(s, i - 1, v);
    }
}

proof fn lemma_count_le_i(s: Seq<i32>, i: int, v: int)
    requires
        0 <= i <= s.len(),
    ensures
        spec_prefix_count(s, i, v) <= i,
    decreases i,
{
    if i <= 0 {
    } else {
        lemma_count_le_i(s, i - 1, v);
        assert(spec_prefix_count(s, i, v) <= spec_prefix_count(s, i - 1, v) + 1);
        assert(spec_prefix_count(s, i, v) <= i);
    }
}

proof fn lemma_prefix_other(s: Seq<i32>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j <= 100,
        s[i] as int != j,
    ensures
        spec_prefix_count(s, i + 1, j) == spec_prefix_count(s, i, j),
{
}

proof fn lemma_prefix_hit(s: Seq<i32>, i: int, j: int)
    requires
        0 <= i < s.len(),
        s[i] as int == j,
    ensures
        spec_prefix_count(s, i + 1, j) == spec_prefix_count(s, i, j) + 1,
{
}

proof fn lemma_cnt_implies_spec_dup(s: Seq<i32>, cnt: Seq<i32>)
    requires
        cnt.len() == 101,
        forall|u: int|
            0 <= u && u <= 100 ==> (cnt[u] as int) == spec_prefix_count(s, s.len() as int, u),
        exists|u: int| 0 <= u && u <= 100 && (cnt[u] as int) >= 2,
    ensures
        spec_has_duplicate(s),
{
    let u = choose|u: int| 0 <= u && u <= 100 && (cnt[u] as int) >= 2;
    assert((cnt[u] as int) == spec_prefix_count(s, s.len() as int, u));
    assert(spec_has_duplicate(s));
}

proof fn lemma_no_dup_cnt(s: Seq<i32>, cnt: Seq<i32>)
    requires
        cnt.len() == 101,
        forall|u: int|
            0 <= u && u <= 100 ==> (cnt[u] as int) == spec_prefix_count(s, s.len() as int, u),
        forall|u: int| 0 <= u && u <= 100 ==> (cnt[u] as int) <= 1,
    ensures
        !spec_has_duplicate(s),
{
    assert forall|vv: int|
        0 <= vv && vv <= 100 implies spec_prefix_count(s, s.len() as int, vv) < 2 by {
        assert((cnt[vv] as int) == spec_prefix_count(s, s.len() as int, vv));
        assert((cnt[vv] as int) <= 1);
    }
}

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn min_ops_to_all_zero(a: Vec<i32>) -> (res: i32)
        requires
            2 <= a.len() <= 100,
            forall|t: int|
                #![trigger a[t]]
                0 <= t < a.len() ==> 0 <= (a[t] as int) <= 100,
        ensures
            (res as int) == spec_min_ops_answer(a@),
    {
        let n = a.len();
        let ghost ni = n as int;
        proof {
            assert(ni == n as int);
            assert(2 <= a.len() && a.len() <= 100);
            assert(2 <= ni && ni <= 100);
        }
        let mut cnt: Vec<i32> = Vec::new();
        let mut t = 0usize;
        while t < 101
            invariant
                t <= 101,
                cnt.len() == t,
                forall|j: int|
                    0 <= j < t as int ==> #[trigger] cnt@[j] == 0,
            decreases 101 - t,
        {
            cnt.push(0i32);
            t = t + 1;
        }
        let mut i = 0usize;
        while i < n
            invariant
                n == a.len(),
                ni == a@.len(),
                ni <= 100,
                i <= n,
                cnt.len() == 101,
                forall|k: int|
                    0 <= k < ni ==> 0 <= #[trigger] a@[k] <= 100,
                forall|j: int|
                    0 <= j < 101 ==> #[trigger] cnt@[j] == spec_prefix_count(a@, i as int, j),
            decreases n - i,
        {
            proof {
                assert(i < n);
                assert(i < a.len());
                assert((i as int) < ni);
                assert(ni == a@.len());
                assert(0 <= a@[i as int] && a@[i as int] <= 100);
            }
            let x = a[i] as usize;
            proof {
                assert(x as int == a@[i as int] as int);
                assert(x <= 100);
                assert(x < cnt.len());
            }
            let prev = cnt[x];
            let ghost i0 = i as int;
            proof {
                assert(i0 < a@.len());
                assert(0 <= a@[i0] && a@[i0] <= 100);
                assert(a@[i0] as int == x as int);
                assert(prev == spec_prefix_count(a@, i0, x as int));
                lemma_spec_prefix_count_nonneg(a@, i0, x as int);
                lemma_count_le_i(a@, i0, x as int);
                assert((prev as int) <= i0);
                assert(i0 < ni);
                assert(ni <= 100);
                assert(i0 <= ni - 1);
                assert((prev as int) <= ni - 1);
                assert(prev + 1 <= ni);
            }
            let ghost cnt0 = cnt@;
            cnt.set(x, prev + 1);
            proof {
                assert forall|j: int|
                    0 <= j < 101 implies cnt@[j] == spec_prefix_count(a@, i0 + 1, j) by {
                    if 0 <= j && j < 101 {
                        if j == x as int {
                            assert(a@[i0] as int == j);
                            lemma_prefix_hit(a@, i0, j);
                            assert(cnt@[j] == prev + 1);
                            assert(spec_prefix_count(a@, i0 + 1, j) == prev + 1);
                        } else {
                            assert(j != x as int);
                            assert(a@[i0] as int == x as int);
                            assert(a@[i0] as int != j);
                            lemma_prefix_other(a@, i0, j);
                            assert(cnt@[j] == cnt0[j]);
                            assert(cnt0[j] == spec_prefix_count(a@, i0, j));
                            assert(cnt@[j] == spec_prefix_count(a@, i0 + 1, j));
                        }
                    }
                };
            }
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert forall|j: int|
                0 <= j < 101 implies cnt@[j] == spec_prefix_count(a@, ni, j) by {
                assert(cnt@[j] == spec_prefix_count(a@, i as int, j));
                assert(i as int == ni);
            }
        }
        let zc = cnt[0];
        proof {
            lemma_spec_prefix_count_nonneg(a@, ni, 0);
            assert((cnt@[0] as int) == spec_prefix_count(a@, ni, 0));
            assert(zc as int >= 0);
        }
        if zc > 0 {
            proof {
                let zn = spec_prefix_count(a@, ni, 0);
                assert(zn == zc as int);
                assert(zn > 0);
                assert(spec_min_ops_answer(a@) == ni - zn);
                assert((n as i32 - zc) as int == ni - zn);
            }
            return n as i32 - zc;
        }
        let mut v = 0usize;
        let mut dup = false;
        while v < 101
            invariant
                cnt.len() == 101,
                v <= 101,
                forall|j: int|
                    0 <= j < 101 ==> #[trigger] cnt@[j] == spec_prefix_count(a@, ni, j),
                dup == exists|x: int|
                    #![trigger cnt@[x]]
                    0 <= x && x < v as int && (cnt@[x] as int) >= 2,
            decreases 101 - v,
        {
            if cnt[v] >= 2 {
                dup = true;
            }
            v = v + 1;
        }
        proof {
            assert(v == 101);
            if dup {
                assert(exists|x: int| 0 <= x && x <= 100 && (cnt@[x] as int) >= 2);
            } else {
                assert forall|x: int|
                    0 <= x && x <= 100 implies (cnt@[x] as int) < 2 by {
                    assert(!(exists|y: int|
                        0 <= y && y < v as int && (cnt@[y] as int) >= 2));
                    assert(x < v as int);
                }
            }
        }
        if dup {
            proof {
                assert(exists|x: int| 0 <= x && x <= 100 && (cnt@[x] as int) >= 2);
                assert forall|u: int|
                    0 <= u && u <= 100 implies (cnt@[u] as int) == spec_prefix_count(a@, ni, u) by {
                }
                lemma_cnt_implies_spec_dup(a@, cnt@);
                assert((cnt@[0] as int) == spec_prefix_count(a@, ni, 0));
                assert(!(zc > 0));
                assert(zc as int >= 0);
                assert(zc == 0);
                assert(spec_prefix_count(a@, ni, 0) == 0);
                assert(spec_min_ops_answer(a@) == ni);
            }
            return n as i32;
        }
        proof {
            assert forall|u: int| 0 <= u && u <= 100 implies (cnt@[u] as int) <= 1 by {
                assert((cnt@[u] as int) < 2);
            }
            lemma_no_dup_cnt(a@, cnt@);
            assert((cnt@[0] as int) == spec_prefix_count(a@, ni, 0));
            assert(!(zc > 0));
            assert(zc as int >= 0);
            assert(zc == 0);
            assert(spec_prefix_count(a@, ni, 0) == 0);
            assert(!spec_has_duplicate(a@));
            assert(spec_min_ops_answer(a@) == ni + 1);
        }
        (n as i32) + 1
    }
}

}
