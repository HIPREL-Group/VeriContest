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

pub open spec fn spec_pair_at_first_half(n: int, t: int) -> (i32, i32)
    recommends
        t < (n + 1) / 2,
{
    let kk = spec_k(n);
    let ii = t + 1;
    ((2 * ii - 1) as i32, (kk - ii) as i32)
}

pub open spec fn spec_pair_at_second_half(n: int, t: int) -> (i32, i32)
    recommends
        (n + 1) / 2 <= t < n,
{
    let kk = spec_k(n);
    let jj = t - (n + 1) / 2 + 1;
    ((2 * jj) as i32, (kk + (n + 1) / 2 - jj - 1) as i32)
}

pub open spec fn spec_pair_at(n: int, t: int) -> (i32, i32)
    recommends
        0 <= t < n,
{
    if t < (n + 1) / 2 {
        spec_pair_at_first_half(n, t)
    } else {
        spec_pair_at_second_half(n, t)
    }
}

pub open spec fn spec_index_for_v(n: int, v: int) -> int {
    let kk = spec_k(n);
    if v % 2 == 1 && v <= n {
        (v - 1) / 2
    } else if v % 2 == 0 && v <= n - 1 {
        (n + 1) / 2 + v / 2 - 1
    } else if kk - (n + 1) / 2 <= v && v <= kk - 1 {
        kk - v - 1
    } else {
        kk + n - 1 - v
    }
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

proof fn lemma_sum_first_half(n: int, t: int)
    requires
        n >= 1,
        n <= 100_000,
        n % 2 == 1,
        0 <= t < (n + 1) / 2,
    ensures
        spec_pair_sum(spec_pair_at(n, t)) == spec_k(n) + t,
{
    let kk = spec_k(n);
    let ii = t + 1;
    let p = spec_pair_at_first_half(n, t);
    assert(spec_pair_at(n, t) == p);
    assert(p.0 == (2 * ii - 1) as i32);
    assert(p.1 == (kk - ii) as i32);
    assert(spec_pair_sum(p) == p.0 as int + p.1 as int);
    assert(spec_pair_sum(p) == (2 * ii - 1) + (kk - ii));
    assert((2 * ii - 1) + (kk - ii) == kk + t);
    assert(spec_pair_sum(spec_pair_at(n, t)) == kk + t);
}

proof fn lemma_sum_second_half(n: int, t: int)
    requires
        n >= 1,
        n <= 100_000,
        n % 2 == 1,
        (n + 1) / 2 <= t < n,
    ensures
        spec_pair_sum(spec_pair_at(n, t)) == spec_k(n) + t,
{
    let kk = spec_k(n);
    let jj = t - (n + 1) / 2 + 1;
    let p = spec_pair_at_second_half(n, t);
    assert(spec_pair_at(n, t) == p);
    assert(p.0 == (2 * jj) as i32);
    assert(p.1 == (kk + (n + 1) / 2 - jj - 1) as i32);
    assert(spec_pair_sum(p) == p.0 as int + p.1 as int);
    assert(spec_pair_sum(p) == (2 * jj) + (kk + (n + 1) / 2 - jj - 1));
    assert((2 * jj) + (kk + (n + 1) / 2 - jj - 1) == kk + t);
    assert(spec_pair_sum(spec_pair_at(n, t)) == kk + t);
}

proof fn lemma_pair_at_sum(n: int, t: int)
    requires
        n >= 1,
        n <= 100_000,
        n % 2 == 1,
        0 <= t < n,
    ensures
        spec_pair_sum(spec_pair_at(n, t)) == spec_k(n) + t,
{
    if t < (n + 1) / 2 {
        lemma_sum_first_half(n, t);
    } else {
        lemma_sum_second_half(n, t);
    }
}

proof fn lemma_unique_index(n: int, v: int, j: int)
    requires
        n >= 1,
        n <= 100_000,
        n % 2 == 1,
        1 <= v <= 2 * n,
        0 <= j < n,
        spec_value_in_pair(spec_pair_at(n, j), v),
    ensures
        j == spec_index_for_v(n, v),
{
    let kk = spec_k(n);
    if j < (n + 1) / 2 {
        let ii = j + 1;
        let p = spec_pair_at_first_half(n, j);
        assert(spec_pair_at(n, j) == p);
        assert(p.0 == (2 * ii - 1) as i32);
        assert(p.1 == (kk - ii) as i32);
        if p.0 as int == v {
            assert(v == 2 * ii - 1);
            assert(v % 2 == 1);
            assert(v <= n);
            assert(j == (v - 1) / 2);
            assert(spec_index_for_v(n, v) == (v - 1) / 2);
        } else {
            assert(p.1 as int == v);
            assert(v == kk - ii);
            assert(ii == kk - v);
            assert(j == ii - 1);
            assert(j == kk - v - 1);
            assert(kk - (n + 1) / 2 <= v && v <= kk - 1);
            assert(spec_index_for_v(n, v) == kk - v - 1);
        }
    } else {
        let jj = j - (n + 1) / 2 + 1;
        let p = spec_pair_at_second_half(n, j);
        assert(spec_pair_at(n, j) == p);
        assert(p.0 == (2 * jj) as i32);
        assert(p.1 == (kk + (n + 1) / 2 - jj - 1) as i32);
        if p.0 as int == v {
            assert(v == 2 * jj);
            assert(v % 2 == 0);
            assert(v <= n - 1);
            assert(j == (n + 1) / 2 + v / 2 - 1);
            assert(spec_index_for_v(n, v) == (n + 1) / 2 + v / 2 - 1);
        } else {
            assert(p.1 as int == v);
            assert(v == kk + (n + 1) / 2 - jj - 1);
            assert(jj == kk + (n + 1) / 2 - 1 - v);
            assert(j == (n + 1) / 2 + jj - 1);
            assert(j == kk + n - 1 - v);
            assert(spec_index_for_v(n, v) == kk + n - 1 - v);
        }
    }
}

proof fn lemma_pair_at_excludes_v_elsewhere(n: int, v: int, idx: int, j: int)
    requires
        n >= 1,
        n <= 100_000,
        n % 2 == 1,
        1 <= v <= 2 * n,
        0 <= idx < n,
        0 <= j < n,
        j != idx,
        spec_value_in_pair(spec_pair_at(n, idx), v),
        idx == spec_index_for_v(n, v),
    ensures
        !spec_value_in_pair(spec_pair_at(n, j), v),
{
    if spec_value_in_pair(spec_pair_at(n, j), v) {
        lemma_unique_index(n, v, j);
        assert(j == spec_index_for_v(n, v));
        assert(j == idx);
        assert(false);
    }
}

proof fn lemma_seq_matches_pair_at(out: Seq<(i32, i32)>, n: int)
    requires
        n >= 1,
        n <= 100_000,
        n % 2 == 1,
        out.len() == n,
        forall|t: int| 0 <= t < n ==> #[trigger] out[t] == spec_pair_at(n, t),
    ensures
        spec_is_valid_pairing(out, n),
{
    let base = spec_k(n);
    assert forall|i: int| 0 <= i < n implies {
        let s = spec_pair_sum(#[trigger] out[i]);
        base <= s <= base + n - 1
    } by {
        assert(out[i] == spec_pair_at(n, i));
        lemma_pair_at_sum(n, i);
        let s = spec_pair_sum(out[i]);
        assert(s == base + i);
        assert(base <= s);
        assert(s <= base + n - 1);
    };
    assert forall|i: int, j: int|
        0 <= i < n && 0 <= j < n && i != j implies spec_pair_sum(out[i]) != spec_pair_sum(out[j]) by {
        lemma_pair_at_sum(n, i);
        lemma_pair_at_sum(n, j);
        assert(spec_pair_sum(out[i]) == base + i);
        assert(spec_pair_sum(out[j]) == base + j);
        assert(base + i != base + j);
    };
    assert forall|v: int| 1 <= v <= 2 * n implies spec_has_value_once(out, n, v) by {
        lemma_has_value_once_pair_at(out, n, v);
    };
}

proof fn lemma_has_value_once_pair_at(out: Seq<(i32, i32)>, n: int, v: int)
    requires
        n >= 1,
        n <= 100_000,
        n % 2 == 1,
        1 <= v <= 2 * n,
        out.len() == n,
        forall|t: int| 0 <= t < n ==> #[trigger] out[t] == spec_pair_at(n, t),
    ensures
        spec_has_value_once(out, n, v),
{
    let idx = spec_index_for_v(n, v);
    assert(0 <= idx < n);
    lemma_idx_contains_v(n, v);
    assert(spec_value_in_pair(spec_pair_at(n, idx), v));
    assert(out[idx] == spec_pair_at(n, idx));
    assert(spec_value_in_pair(out[idx], v));
    assert forall|j: int| 0 <= j < n && j != idx implies !spec_value_in_pair(out[j], v) by {
        assert(out[j] == spec_pair_at(n, j));
        lemma_pair_at_excludes_v_elsewhere(n, v, idx, j);
    };
    assert(spec_has_value_once(out, n, v));
}

proof fn lemma_idx_contains_v(n: int, v: int)
    requires
        n >= 1,
        n <= 100_000,
        n % 2 == 1,
        1 <= v <= 2 * n,
    ensures
        spec_value_in_pair(spec_pair_at(n, spec_index_for_v(n, v)), v),
{
    let idx = spec_index_for_v(n, v);
    let kk = spec_k(n);
    if v % 2 == 1 && v <= n {
        assert(idx == (v - 1) / 2);
        assert(idx < (n + 1) / 2);
        let p = spec_pair_at_first_half(n, idx);
        assert(spec_pair_at(n, idx) == p);
        assert(p.0 == (2 * (idx + 1) - 1) as i32);
        assert(2 * (idx + 1) - 1 == v);
        assert(spec_value_in_pair(p, v));
    } else if v % 2 == 0 && v <= n - 1 {
        assert(idx == (n + 1) / 2 + v / 2 - 1);
        assert(idx >= (n + 1) / 2);
        let p = spec_pair_at_second_half(n, idx);
        assert(spec_pair_at(n, idx) == p);
        assert(p.0 == (2 * (idx - (n + 1) / 2 + 1)) as i32);
        assert(2 * (idx - (n + 1) / 2 + 1) == v);
        assert(spec_value_in_pair(p, v));
    } else if kk - (n + 1) / 2 <= v && v <= kk - 1 {
        assert(idx == kk - v - 1);
        assert(idx < (n + 1) / 2);
        let ii = idx + 1;
        let p = spec_pair_at_first_half(n, idx);
        assert(spec_pair_at(n, idx) == p);
        assert(p.1 == (kk - ii) as i32);
        assert(kk - ii == v);
        assert(spec_value_in_pair(p, v));
    } else {
        assert(idx == kk + n - 1 - v);
        assert(idx >= (n + 1) / 2);
        let jj = idx - (n + 1) / 2 + 1;
        let p = spec_pair_at_second_half(n, idx);
        assert(spec_pair_at(n, idx) == p);
        assert(p.1 == (kk + (n + 1) / 2 - jj - 1) as i32);
        assert(kk + (n + 1) / 2 - jj - 1 == v);
        assert(spec_value_in_pair(p, v));
    }
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
        while i <= (n + 1) / 2
            invariant
                n % 2 == 1,
                1 <= n <= 100_000,
                k == (3 * n + 3) / 2,
                1 <= i <= (n + 1) / 2 + 1,
                out.len() == i - 1,
                forall|t: int|
                    0 <= t < i - 1 ==> #[trigger] out@[t] == spec_pair_at(n as int, t),
            decreases (n + 1) / 2 + 1 - i,
        {
            let a1: i32 = 2 * i - 1;
            let b1: i32 = k - i;
            proof {
                let t = i - 1;
                assert(0 <= t < (n + 1) / 2);
                assert(spec_pair_at(n as int, t) == ((2 * i - 1) as i32, (k - i) as i32));
            }
            out.push((a1, b1));
            i = i + 1;
        }
        let ghost first_len: int = (n + 1) / 2;
        proof {
            assert(out@.len() == first_len);
            assert forall|t: int| 0 <= t < first_len implies #[trigger] out@[t] == spec_pair_at(n as int, t) by {
            };
        }
        let mut j: i32 = 1;
        while j <= (n - 1) / 2
            invariant
                n % 2 == 1,
                1 <= n <= 100_000,
                k == (3 * n + 3) / 2,
                first_len == (n + 1) / 2,
                out.len() == first_len + j - 1,
                1 <= j <= (n - 1) / 2 + 1,
                forall|t: int|
                    0 <= t < first_len ==> #[trigger] out@[t] == spec_pair_at(n as int, t),
                forall|t: int|
                    first_len <= t < first_len + j - 1 ==> #[trigger] out@[t] == spec_pair_at(n as int, t),
            decreases (n - 1) / 2 + 1 - j,
        {
            let a2: i32 = 2 * j;
            let b2: i32 = k + (n + 1) / 2 - j - 1;
            proof {
                let t = first_len + j - 1;
                assert(t == (n + 1) / 2 + j - 1);
                assert(t >= (n + 1) / 2);
                assert(j <= (n - 1) / 2);
                assert(t < n);
                assert(spec_pair_at(n as int, t) == ((2 * j) as i32, (k + (n + 1) / 2 - j - 1) as i32));
            }
            out.push((a2, b2));
            j = j + 1;
        }
        proof {
            assert(out@.len() == n as int);
            assert forall|t: int| 0 <= t < n as int implies #[trigger] out@[t] == spec_pair_at(n as int, t) by {
                if t < first_len {
                } else {
                    assert(t >= first_len);
                    assert(t < n);
                }
            };
            lemma_seq_matches_pair_at(out@, n as int);
        }
        Some(out)
    }
}

}
