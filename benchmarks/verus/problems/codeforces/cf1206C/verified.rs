use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_entry_at(k: int, n: int) -> int {
        if k < n {
            if k % 2 == 0 { 2 * k + 1 } else { 2 * k + 2 }
        } else {
            let j = k - n;
            if j % 2 == 0 { 2 * j + 2 } else { 2 * j + 1 }
        }
    }

    pub open spec fn spec_is_permutation(arr: Seq<i64>, n: int) -> bool {
        arr.len() == 2 * n
        && (forall|i: int| 0 <= i < 2 * n ==> 1 <= #[trigger] arr[i] <= 2 * n)
        && (forall|i: int, j: int| 0 <= i < j < 2 * n ==> #[trigger] arr[i] != #[trigger] arr[j])
    }

    pub open spec fn spec_circular_sum(a: Seq<i64>, n: int, start: int, count: int) -> int
        decreases count,
    {
        if count <= 0 {
            0int
        } else {
            a[start % (2 * n)] + Self::spec_circular_sum(a, n, start + 1, count - 1)
        }
    }

    pub open spec fn spec_all_sums_close(a: Seq<i64>, n: int) -> bool {
        forall|i: int, j: int|
            #![trigger Self::spec_circular_sum(a, n, i, n), Self::spec_circular_sum(a, n, j, n)]
            0 <= i < 2 * n && 0 <= j < 2 * n ==> {
                let diff = Self::spec_circular_sum(a, n, i, n) - Self::spec_circular_sum(a, n, j, n);
                -1 <= diff && diff <= 1
            }
    }

    proof fn lemma_entry_at_push(n: int, i: int)
        requires
            1 <= n <= 100000,
            0 <= i < n,
        ensures
            Self::spec_entry_at(i, n) == (if i % 2 == 0 { 2 * i + 1 } else { 2 * i + 2 }),
            Self::spec_entry_at(i + n, n) == (if i % 2 == 0 { 2 * i + 2 } else { 2 * i + 1 }),
    {
    }

    proof fn lemma_seq_is_permutation(s: Seq<i64>, n: int)
        requires
            1 <= n <= 100000,
            n % 2 == 1,
            s.len() == 2 * n,
            forall|k: int|
                #![trigger s[k]]
                0 <= k < 2 * n ==> s[k] as int == Self::spec_entry_at(k, n),
        ensures
            Self::spec_is_permutation(s, n),
    {
        assert forall|k: int| 0 <= k < 2 * n implies 1 <= #[trigger] s[k] <= 2 * n by {
            assert(s[k] as int == Self::spec_entry_at(k, n));
        };
        assert forall|i: int, j: int| 0 <= i < j < 2 * n implies
            #[trigger] s[i] != #[trigger] s[j]
        by {
            assert(s[i] as int == Self::spec_entry_at(i, n));
            assert(s[j] as int == Self::spec_entry_at(j, n));
            let pi = if i < n { i } else { i - n };
            let pj = if j < n { j } else { j - n };
            if pi < pj {
                assert(Self::spec_entry_at(i, n) <= 2 * pi + 2);
                assert(Self::spec_entry_at(j, n) >= 2 * pj + 1);
                assert(2 * pj + 1 > 2 * pi + 2) by (nonlinear_arith)
                    requires pi + 1 <= pj;
            } else if pj < pi {
                assert(Self::spec_entry_at(i, n) >= 2 * pi + 1);
                assert(Self::spec_entry_at(j, n) <= 2 * pj + 2);
                assert(2 * pi + 1 > 2 * pj + 2) by (nonlinear_arith)
                    requires pj + 1 <= pi;
            } else {
                
                assert(i < n && j >= n);
            }
        };
    }

    proof fn lemma_sum_snoc(a: Seq<i64>, n: int, start: int, count: int)
        requires
            a.len() == 2 * n,
            n >= 1,
            start >= 0,
            count >= 1,
        ensures
            Self::spec_circular_sum(a, n, start, count) ==
            Self::spec_circular_sum(a, n, start, count - 1) + a[(start + count - 1) % (2 * n)],
        decreases count,
    {
        reveal_with_fuel(Solution::spec_circular_sum, 2);
        if count > 1 {
            Self::lemma_sum_snoc(a, n, start + 1, count - 1);
        }
    }

    proof fn lemma_window_step(a: Seq<i64>, n: int, start: int)
        requires
            a.len() == 2 * n,
            n >= 1,
            start >= 0,
        ensures
            Self::spec_circular_sum(a, n, start + 1, n) ==
            Self::spec_circular_sum(a, n, start, n) + a[(start + n) % (2 * n)] - a[start % (2 * n)],
    {
        Self::lemma_sum_snoc(a, n, start + 1, n);
    }

    proof fn lemma_entry_diff(s: Seq<i64>, n: int, i: int)
        requires
            1 <= n <= 100000,
            n % 2 == 1,
            s.len() == 2 * n,
            forall|k: int|
                #![trigger s[k]]
                0 <= k < 2 * n ==> s[k] as int == Self::spec_entry_at(k, n),
            0 <= i < 2 * n,
        ensures
            s[(i + n) % (2 * n)] as int - s[i] as int == (if i % 2 == 0 { 1int } else { -1int }),
    {
        let opp = (i + n) % (2 * n);
        assert(s[i] as int == Self::spec_entry_at(i, n));
        assert(0 <= opp < 2 * n);
        assert(s[opp] as int == Self::spec_entry_at(opp, n));
        if i < n {
            assert(opp == i + n) by (nonlinear_arith)
                requires 0 <= i < n, n >= 1, opp == (i + n) % (2 * n);
        } else {
            assert(opp == i - n) by (nonlinear_arith)
                requires n <= i < 2 * n, n >= 1, opp == (i + n) % (2 * n);
            let j = i - n;
            if j % 2 == 0 {
                assert(i % 2 == 1) by (nonlinear_arith)
                    requires i == j + n, j % 2 == 0, n % 2 == 1;
            } else {
                assert(i % 2 == 0) by (nonlinear_arith)
                    requires i == j + n, j % 2 == 1, n % 2 == 1;
            }
        }
    }

    proof fn lemma_window_parity(s: Seq<i64>, n: int, start: int)
        requires
            1 <= n <= 100000,
            n % 2 == 1,
            s.len() == 2 * n,
            forall|k: int|
                #![trigger s[k]]
                0 <= k < 2 * n ==> s[k] as int == Self::spec_entry_at(k, n),
            0 <= start < 2 * n,
        ensures
            Self::spec_circular_sum(s, n, start, n) ==
            Self::spec_circular_sum(s, n, 0, n) + start % 2,
        decreases start,
    {
        if start > 0 {
            Self::lemma_window_parity(s, n, start - 1);
            Self::lemma_window_step(s, n, start - 1);
            Self::lemma_entry_diff(s, n, start - 1);
            assert((start - 1) % (2 * n) == start - 1) by (nonlinear_arith)
                requires 0 <= start - 1 < 2 * n, n >= 1;
            if (start - 1) % 2 == 0 {
                assert(start % 2 == 1) by (nonlinear_arith)
                    requires start >= 1, (start - 1) % 2 == 0;
            } else {
                assert(start % 2 == 0) by (nonlinear_arith)
                    requires start >= 1, (start - 1) % 2 == 1;
            }
        }
    }

    proof fn lemma_all_sums_close(s: Seq<i64>, n: int)
        requires
            1 <= n <= 100000,
            n % 2 == 1,
            s.len() == 2 * n,
            forall|k: int|
                #![trigger s[k]]
                0 <= k < 2 * n ==> s[k] as int == Self::spec_entry_at(k, n),
        ensures
            Self::spec_all_sums_close(s, n),
    {
        assert forall|i: int, j: int|
            #![trigger Self::spec_circular_sum(s, n, i, n), Self::spec_circular_sum(s, n, j, n)]
            0 <= i < 2 * n && 0 <= j < 2 * n implies {
                let diff = Self::spec_circular_sum(s, n, i, n) - Self::spec_circular_sum(s, n, j, n);
                -1 <= diff && diff <= 1
            }
        by {
            Self::lemma_window_parity(s, n, i);
            Self::lemma_window_parity(s, n, j);
        };
    }

    pub fn almost_equal(n: usize) -> (res: Vec<i64>)
        requires
            1 <= n <= 100000,
        ensures
            n % 2 == 0 ==> res.len() == 0,
            n % 2 == 1 ==> (
                Self::spec_is_permutation(res@, n as int)
                && Self::spec_all_sums_close(res@, n as int)
            ),
    {
        if n % 2 == 0 {
            return Vec::new();
        }
        let mut res: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 100000,
                n % 2 == 1,
                i <= n,
                res.len() == i,
                forall|k: int|
                    #![trigger res@[k]]
                    0 <= k < i as int ==> res@[k] as int == Self::spec_entry_at(k, n as int),
            decreases n - i,
        {
            proof {
                Self::lemma_entry_at_push(n as int, i as int);
            }
            if i % 2 == 0 {
                res.push((2 * i + 1) as i64);
            } else {
                res.push((2 * i + 2) as i64);
            }
            i = i + 1;
        }
        i = 0;
        while i < n
            invariant
                1 <= n <= 100000,
                n % 2 == 1,
                i <= n,
                res.len() == n + i,
                forall|k: int|
                    #![trigger res@[k]]
                    0 <= k < n as int ==> res@[k] as int == Self::spec_entry_at(k, n as int),
                forall|k: int|
                    #![trigger res@[k]]
                    n as int <= k < (n + i) as int ==> res@[k] as int == Self::spec_entry_at(k, n as int),
            decreases n - i,
        {
            proof {
                Self::lemma_entry_at_push(n as int, i as int);
            }
            if i % 2 == 0 {
                res.push((2 * i + 2) as i64);
            } else {
                res.push((2 * i + 1) as i64);
            }
            i = i + 1;
        }
        proof {
            assert forall|k: int|
                #![trigger res@[k]]
                0 <= k < 2 * n as int implies res@[k] as int == Self::spec_entry_at(k, n as int)
            by {};
            Self::lemma_seq_is_permutation(res@, n as int);
            Self::lemma_all_sums_close(res@, n as int);
        }
        res
    }
}

}