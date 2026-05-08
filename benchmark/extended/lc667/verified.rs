use vstd::prelude::*;
use vstd::seq::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn adj_diff(s: Seq<i32>, i: int) -> int {
        if s[i] as int >= s[i + 1] as int {
            s[i] as int - s[i + 1] as int
        } else {
            s[i + 1] as int - s[i] as int
        }
    }

    pub open spec fn zigzag_val(i: int, k: int) -> int {
        if i % 2 == 0 {
            1 + i / 2
        } else {
            (k + 1) - (i - 1) / 2
        }
    }

    proof fn lemma_zigzag_val_range(j: int, k: int, n: int)
        requires 0 <= j <= k, 1 <= k < n,
        ensures 1 <= Self::zigzag_val(j, k) <= n,
        decreases j,
    {
        if j % 2 == 0 {
            assert(Self::zigzag_val(j, k) == 1 + j / 2);
        } else {
            assert(Self::zigzag_val(j, k) == (k + 1) - (j - 1) / 2);
        }
    }

    proof fn lemma_zigzag_in_range(j: int, k: int)
        requires 0 <= j <= k, k >= 1,
        ensures 1 <= Self::zigzag_val(j, k) <= k + 1,
    {
        if j % 2 == 0 {
            assert(Self::zigzag_val(j, k) == 1 + j / 2);
            assert(j / 2 <= k / 2);
            assert(1 + k / 2 <= k + 1);
        } else {
            assert(Self::zigzag_val(j, k) == (k + 1) - (j - 1) / 2);
            assert((j - 1) / 2 <= (k - 1) / 2);
            assert((k + 1) - (k - 1) / 2 >= 1);
        }
    }

    proof fn lemma_zigzag_injective(i: int, j: int, k: int)
        requires 0 <= i <= k, 0 <= j <= k, i != j, k >= 1,
        ensures Self::zigzag_val(i, k) != Self::zigzag_val(j, k),
    {
        if i % 2 == 0 && j % 2 == 0 {
            assert(Self::zigzag_val(i, k) == 1 + i / 2);
            assert(Self::zigzag_val(j, k) == 1 + j / 2);
            assert(i / 2 != j / 2);
        } else if i % 2 == 1 && j % 2 == 1 {
            assert(Self::zigzag_val(i, k) == (k + 1) - (i - 1) / 2);
            assert(Self::zigzag_val(j, k) == (k + 1) - (j - 1) / 2);
            assert((i - 1) / 2 != (j - 1) / 2);
        } else if i % 2 == 0 && j % 2 == 1 {
            assert(Self::zigzag_val(i, k) == 1 + i / 2);
            assert(Self::zigzag_val(j, k) == (k + 1) - (j - 1) / 2);
            assert(1 + i / 2 <= 1 + k / 2);
            assert((k + 1) - (j - 1) / 2 >= (k + 1) - (k - 1) / 2);
            assert(k / 2 + (k - 1) / 2 <= k - 1) by (nonlinear_arith) requires k >= 1;
            assert(1 + k / 2 < (k + 1) - (k - 1) / 2);
        } else {
            assert(Self::zigzag_val(j, k) == 1 + j / 2);
            assert(Self::zigzag_val(i, k) == (k + 1) - (i - 1) / 2);
            assert(1 + j / 2 <= 1 + k / 2);
            assert((k + 1) - (i - 1) / 2 >= (k + 1) - (k - 1) / 2);
            assert(k / 2 + (k - 1) / 2 <= k - 1) by (nonlinear_arith) requires k >= 1;
            assert(1 + k / 2 < (k + 1) - (k - 1) / 2);
        }
    }

    proof fn lemma_zigzag_adj_diff(s: Seq<i32>, j: int, k: int)
        requires
            0 <= j < k, k >= 1,
            s.len() > k,
            forall |i: int| 0 <= i <= k ==> s[i] == Self::zigzag_val(i, k),
        ensures
            Self::adj_diff(s, j) == k - j,
    {
        let v0 = Self::zigzag_val(j, k);
        let v1 = Self::zigzag_val(j + 1, k);
        assert(s[j] as int == v0);
        assert(s[j + 1] as int == v1);

        if j % 2 == 0 {
            assert(v0 == 1 + j / 2);
            assert(v1 == (k + 1) - ((j + 1) - 1) / 2);
            assert(((j + 1) - 1) / 2 == j / 2);
            assert(v1 == (k + 1) - j / 2);
            assert(v1 - v0 == k - j);
            assert(v1 > v0);
        } else {
            assert(v0 == (k + 1) - (j - 1) / 2);
            assert(v1 == 1 + (j + 1) / 2);
            assert((j + 1) / 2 == (j - 1) / 2 + 1);
            assert(v1 == 2 + (j - 1) / 2);
            assert(v0 - v1 == k - j);
            assert(v0 > v1);
        }
    }

    proof fn lemma_transition_adj_diff(s: Seq<i32>, k: int, n: int)
        requires
            1 <= k, k + 1 < n, n <= 10_000,
            s.len() == n,
            forall |i: int| 0 <= i <= k ==> s[i] == Self::zigzag_val(i, k),
            s[k + 1] as int == k + 2,
        ensures
            Self::adj_diff(s, k) == k - (k - 1) / 2,
    {
        let vk = Self::zigzag_val(k, k);
        assert(s[k] as int == vk);
        assert(s[k + 1] as int == k + 2);

        if k % 2 == 0 {
            assert(vk == 1 + k / 2);
            assert(k + 2 - vk == k / 2 + 1);
            assert((k - 1) / 2 == k / 2 - 1) by (nonlinear_arith)
                requires k % 2 == 0, k >= 2;
            if k >= 2 {
                assert(k / 2 + 1 == k - (k - 1) / 2);
            }
            assert(k + 2 > vk);
        } else {
            assert(vk == (k + 1) - (k - 1) / 2);
            assert(k + 2 - vk == 1 + (k - 1) / 2);
            assert(1 + (k - 1) / 2 == k - (k - 1) / 2) by (nonlinear_arith)
                requires k % 2 == 1, k >= 1;
            assert(k + 2 > vk);
        }
    }

    pub open spec fn witness_indices(k: int) -> Seq<int>
        decreases k,
    {
        if k <= 0 {
            Seq::empty()
        } else {
            Self::witness_indices(k - 1).push(k - 1)
        }
    }

    proof fn lemma_witness_len(k: int)
        requires k >= 0,
        ensures Self::witness_indices(k).len() == k,
        decreases k,
    {
        if k > 0 {
            Self::lemma_witness_len(k - 1);
        }
    }

    proof fn lemma_witness_idx(k: int, a: int)
        requires 0 <= a < k,
        ensures Self::witness_indices(k)[a] == a,
        decreases k,
    {
        Self::lemma_witness_len(k);
        if k > 0 {
            if a < k - 1 {
                Self::lemma_witness_idx(k - 1, a);
                let s = Self::witness_indices(k - 1);
                axiom_seq_push_index_different(s, k - 1, a);
            } else {
                Self::lemma_witness_len(k - 1);
                let s = Self::witness_indices(k - 1);
                axiom_seq_push_index_same(s, k - 1, k - 1);
            }
        }
    }

    pub fn construct_array(n: i32, k: i32) -> (result: Vec<i32>)
        requires
            1 <= k < n <= 10_000,
        ensures
            result@.len() == n as int,
            forall |i: int| 0 <= i < result@.len() ==>
                1 <= #[trigger] result@[i] <= n,
            forall |i: int, j: int|
                0 <= i < j < result@.len() ==> result@[i] != result@[j],
            exists |indices: Seq<int>|
                indices.len() == k as int
                && forall |a: int| 0 <= a < indices.len() ==>
                    0 <= #[trigger] indices[a] < result@.len() - 1
                && forall |a: int, b: int|
                    0 <= a < b < indices.len() ==>
                    #[trigger] Self::adj_diff(result@, indices[a]) != #[trigger] Self::adj_diff(result@, indices[b])
                && forall |j: int| 0 <= j < result@.len() - 1 ==>
                    exists |a: int| 0 <= a < indices.len()
                    && #[trigger] Self::adj_diff(result@, j) == Self::adj_diff(result@, indices[a]),
    {
        let mut result = Vec::new();
        let mut i: usize = 0;
        while i < n as usize
            invariant
                1 <= k < n <= 10_000,
                0 <= i <= n as usize,
                result.len() == i,
                forall |j: int| 0 <= j < i ==> result@[j] == 0,
            decreases (n as usize) - i,
        {
            result.push(0);
            i += 1;
        }

        let mut idx: usize = 0;
        while idx <= k as usize
            invariant
                1 <= k < n <= 10_000,
                result@.len() == n as int,
                0 <= idx <= (k as usize) + 1,
                forall |j: int| 0 <= j < idx as int ==>
                    result@[j] == Self::zigzag_val(j, k as int),
                forall |j: int| idx as int <= j < n ==>
                    result@[j] == 0,
            decreases (k as usize) + 1 - idx,
        {
            let val = if idx % 2 == 0 {
                1 + (idx as i32) / 2
            } else {
                (k + 1) - ((idx as i32) - 1) / 2
            };
            proof {
                Self::lemma_zigzag_val_range(idx as int, k as int, n as int);
            }
            result[idx] = val;
            idx += 1;
        }

        let mut idx2 = idx;
        while idx2 < n as usize
            invariant
                1 <= k < n <= 10_000,
                result@.len() == n as int,
                k as usize + 1 <= idx2 <= n as usize,
                forall |j: int| 0 <= j <= k as int ==>
                    result@[j] == Self::zigzag_val(j, k as int),
                forall |j: int| (k as usize + 1) as int <= j < idx2 as int ==>
                    result@[j] == (j + 1) as i32,
                forall |j: int| idx2 as int <= j < n ==>
                    result@[j] == 0,
            decreases (n as usize) - idx2,
        {
            result[idx2] = (idx2 as i32) + 1;
            idx2 += 1;
        }

        proof {
            let s = result@;
            let ki = k as int;
            let ni = n as int;
            assert forall |i: int| 0 <= i < s.len() implies
                1 <= #[trigger] s[i] <= n by {
                if i <= ki {
                    Self::lemma_zigzag_val_range(i, ki, ni);
                } else {
                    assert(s[i] == (i + 1) as i32);
                }
            };

            assert forall |i: int, j: int| 0 <= i < j < s.len()
                implies s[i] != s[j] by {
                if i <= ki && j <= ki {
                    Self::lemma_zigzag_injective(i, j, ki);
                } else if i > ki && j > ki {
                    assert(s[i] == (i + 1) as i32);
                    assert(s[j] == (j + 1) as i32);
                } else {
                    Self::lemma_zigzag_in_range(i, ki);
                    assert(s[i] as int == Self::zigzag_val(i, ki));
                    assert(Self::zigzag_val(i, ki) <= ki + 1);
                    assert(s[j] == (j + 1) as i32);
                    assert(s[j] as int == j + 1);
                    assert(j + 1 >= ki + 2);
                }
            };

            let indices = Self::witness_indices(ki);
            Self::lemma_witness_len(ki);

            assert forall |a: int| 0 <= a < indices.len() implies
                0 <= #[trigger] indices[a] < s.len() - 1 by {
                Self::lemma_witness_idx(ki, a);
            };

            assert forall |a: int, b: int|
                0 <= a < b < indices.len() implies
                #[trigger] Self::adj_diff(s, indices[a]) != #[trigger] Self::adj_diff(s, indices[b]) by {
                Self::lemma_witness_idx(ki, a);
                Self::lemma_witness_idx(ki, b);
                Self::lemma_zigzag_adj_diff(s, a, ki);
                Self::lemma_zigzag_adj_diff(s, b, ki);
            };

            assert forall |j: int| 0 <= j < s.len() - 1 implies
                exists |a: int| 0 <= a < indices.len()
                && #[trigger] Self::adj_diff(s, j) == Self::adj_diff(s, indices[a]) by {
                if j < ki {
                    Self::lemma_witness_idx(ki, j);
                    assert(Self::adj_diff(s, j) == Self::adj_diff(s, indices[j]));
                } else if j > ki {
                    assert(s[j] == (j + 1) as i32);
                    assert(s[j + 1] == (j + 2) as i32);
                    assert(Self::adj_diff(s, j) == 1);
                    Self::lemma_witness_idx(ki, ki - 1);
                    Self::lemma_zigzag_adj_diff(s, ki - 1, ki);
                    assert(Self::adj_diff(s, indices[ki - 1]) == 1);
                } else {
                    assert(j == ki);
                    if ki + 1 < ni {
                        assert(s[ki + 1] == (ki + 2) as i32);
                        Self::lemma_transition_adj_diff(s, ki, ni);
                        assert(Self::adj_diff(s, ki) == ki - (ki - 1) / 2);
                        let w = (ki - 1) / 2;
                        assert(0 <= w < ki);
                        Self::lemma_witness_idx(ki, w);
                        Self::lemma_zigzag_adj_diff(s, w, ki);
                        assert(Self::adj_diff(s, indices[w]) == ki - w);
                        assert(ki - w == ki - (ki - 1) / 2);
                    } else {
                        assert(false);
                    }
                }
            };
        }
        result
    }
}

}
