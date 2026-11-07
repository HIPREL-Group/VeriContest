use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn dot_prefix(a: Seq<i32>, b: Seq<i32>, i: int) -> int
        recommends
            a.len() == b.len(),
            0 <= i <= a.len(),
        decreases i,
    {
        if i <= 0 {
            0
        } else {
            Self::dot_prefix(a, b, i - 1) + (a[i - 1] as int) * (b[i - 1] as int)
        }
    }

    pub open spec fn dot(a: Seq<i32>, b: Seq<i32>) -> int
        recommends
            a.len() == b.len(),
    {
        Self::dot_prefix(a, b, a.len() as int)
    }

    pub open spec fn abs_val(x: i32) -> int {
        if x >= 0 { x as int } else { -(x as int) }
    }

    pub open spec fn abs_sum_prefix(b: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::abs_sum_prefix(b, n - 1) + Self::abs_val(b[n - 1])
        }
    }

    pub open spec fn valid_coeffs(a: Seq<i32>, b: Seq<i32>) -> bool {
        &&& a.len() == b.len()
        &&& 2 <= a.len()
        &&& forall|i: int| 0 <= i < a.len() ==> #[trigger] b[i] != 0
        &&& Self::dot(a, b) == 0
        &&& Self::abs_sum_prefix(b, b.len() as int) <= 1_000_000_000
    }

    proof fn lemma_pair_prefix(a: Seq<i32>, b: Seq<i32>, i: int)
        requires
            a.len() == b.len(),
            0 <= i,
            i + 1 < a.len(),
        ensures
            Self::dot_prefix(a, b, i + 2)
                == Self::dot_prefix(a, b, i)
                    + (a[i] as int) * (b[i] as int)
                    + (a[i + 1] as int) * (b[i + 1] as int),
    {
        assert(Self::dot_prefix(a, b, i + 2)
            == Self::dot_prefix(a, b, i + 1) + (a[i + 1] as int) * (b[i + 1] as int));
        assert(Self::dot_prefix(a, b, i + 1)
            == Self::dot_prefix(a, b, i) + (a[i] as int) * (b[i] as int));
    }

    proof fn lemma_even_pairs_zero(a: Seq<i32>, b: Seq<i32>, i: int, n: int)
        requires
            a.len() == b.len(),
            0 <= i <= n <= a.len(),
            (n - i) % 2 == 0,
            forall|j: int|
                i <= j < n && (j - i) % 2 == 0
                    ==> (a[j] as int) * (#[trigger] b[j] as int) + (a[j + 1] as int) * (b[j + 1] as int) == 0,
        ensures
            Self::dot_prefix(a, b, n) == Self::dot_prefix(a, b, i),
        decreases n - i,
    {
        if i < n {
            Self::lemma_even_pairs_zero(a, b, i + 2, n);
            Self::lemma_pair_prefix(a, b, i);
            assert((a[i] as int) * (b[i] as int) + (a[i + 1] as int) * (b[i + 1] as int) == 0);
        }
    }

    proof fn lemma_abs_sum_prefix_step(b: Seq<i32>, i: int)
        requires
            0 <= i,
            i < b.len(),
        ensures
            Self::abs_sum_prefix(b, i + 1) == Self::abs_sum_prefix(b, i) + Self::abs_val(b[i]),
    {
    }

    proof fn lemma_abs_sum_prefix_append_invariant(b1: Seq<i32>, b2: Seq<i32>, n: int)
        requires
            0 <= n <= b1.len(),
            b1.len() <= b2.len(),
            forall|k: int| 0 <= k < n ==> b1[k] == b2[k],
        ensures
            Self::abs_sum_prefix(b1, n) == Self::abs_sum_prefix(b2, n),
        decreases n,
    {
        if n > 0 {
            Self::lemma_abs_sum_prefix_append_invariant(b1, b2, n - 1);
        }
    }

    proof fn lemma_pair_abs_bound(b: Seq<i32>, i: int, n: int)
        requires
            0 <= i <= n <= b.len(),
            (n - i) % 2 == 0,
            forall|j: int|
                i <= j < n && (j - i) % 2 == 0
                    ==> #[trigger] Self::abs_val(b[j]) + Self::abs_val(b[j + 1]) <= 20000,
        ensures
            Self::abs_sum_prefix(b, n) <= Self::abs_sum_prefix(b, i) + 10000 * (n - i),
        decreases n - i,
    {
        if i < n {
            Self::lemma_pair_abs_bound(b, i + 2, n);
            Self::lemma_abs_sum_prefix_step(b, i);
            Self::lemma_abs_sum_prefix_step(b, i + 1);
            assert(Self::abs_val(b[i]) + Self::abs_val(b[i + 1]) <= 20000);
        }
    }

    pub fn construct_coeffs(a: Vec<i32>) -> (b: Vec<i32>)
        requires
            2 <= a.len() <= 100000,
            forall|i: int| 0 <= i < a.len() ==> -10000 <= #[trigger] a[i] <= 10000,
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] != 0,
        ensures
            Self::valid_coeffs(a@, b@),
    {
        let n = a.len();
        let mut b: Vec<i32> = Vec::new();

        if n % 2 == 1 {
            let x0 = a[0];
            let x1 = a[1];
            let x2 = a[2];
            proof {
                assert(-10000 <= a@[0] as int <= 10000);
                assert(-10000 <= a@[1] as int <= 10000);
                assert(-10000 <= a@[2] as int <= 10000);
            }
            if x0 + x1 != 0 {
                b.push(x2);
                b.push(x2);
                b.push(-(x0 + x1));
                proof {
                    assert(b@.len() == 3);
                    assert(b@[0] == x2);
                    assert(b@[1] == x2);
                    assert(b@[2] == -(x0 + x1));
                    assert(b@[0] != 0);
                    assert(b@[1] != 0);
                    assert(b@[2] != 0);
                    assert((a@[0] as int) * (b@[0] as int)
                        + (a@[1] as int) * (b@[1] as int)
                        + (a@[2] as int) * (b@[2] as int) == 0) by (nonlinear_arith)
                        requires
                            b@[0] == x2,
                            b@[1] == x2,
                            b@[2] == -(x0 + x1),
                            a@[0] == x0,
                            a@[1] == x1,
                            a@[2] == x2;
                    assert(Self::abs_sum_prefix(b@, 1)
                        == Self::abs_sum_prefix(b@, 0) + Self::abs_val(b@[0]));
                    assert(Self::abs_sum_prefix(b@, 2)
                        == Self::abs_sum_prefix(b@, 1) + Self::abs_val(b@[1]));
                    assert(Self::abs_sum_prefix(b@, 3)
                        == Self::abs_sum_prefix(b@, 2) + Self::abs_val(b@[2]));
                    assert(Self::abs_sum_prefix(b@, 0) == 0);
                    assert(Self::abs_sum_prefix(b@, 3) <= 40000);
                }
            } else if x0 + x2 != 0 {
                b.push(x1);
                b.push(-(x0 + x2));
                b.push(x1);
                proof {
                    assert(b@.len() == 3);
                    assert(b@[0] == x1);
                    assert(b@[1] == -(x0 + x2));
                    assert(b@[2] == x1);
                    assert(b@[0] != 0);
                    assert(b@[1] != 0);
                    assert(b@[2] != 0);
                    assert((a@[0] as int) * (b@[0] as int)
                        + (a@[1] as int) * (b@[1] as int)
                        + (a@[2] as int) * (b@[2] as int) == 0) by (nonlinear_arith)
                        requires
                            b@[0] == x1,
                            b@[1] == -(x0 + x2),
                            b@[2] == x1,
                            a@[0] == x0,
                            a@[1] == x1,
                            a@[2] == x2;
                    assert(Self::abs_sum_prefix(b@, 1)
                        == Self::abs_sum_prefix(b@, 0) + Self::abs_val(b@[0]));
                    assert(Self::abs_sum_prefix(b@, 2)
                        == Self::abs_sum_prefix(b@, 1) + Self::abs_val(b@[1]));
                    assert(Self::abs_sum_prefix(b@, 3)
                        == Self::abs_sum_prefix(b@, 2) + Self::abs_val(b@[2]));
                    assert(Self::abs_sum_prefix(b@, 0) == 0);
                    assert(Self::abs_sum_prefix(b@, 3) <= 40000);
                }
            } else {
                b.push(-(x1 + x2));
                b.push(x0);
                b.push(x0);
                proof {
                    assert(x0 + x1 == 0);
                    assert(x0 + x2 == 0);
                    assert(x1 + x2 != 0) by (nonlinear_arith)
                        requires
                            x0 + x1 == 0,
                            x0 + x2 == 0,
                            x0 != 0;
                    assert(b@.len() == 3);
                    assert(b@[0] == -(x1 + x2));
                    assert(b@[1] == x0);
                    assert(b@[2] == x0);
                    assert(b@[0] != 0);
                    assert(b@[1] != 0);
                    assert(b@[2] != 0);
                    assert((a@[0] as int) * (b@[0] as int)
                        + (a@[1] as int) * (b@[1] as int)
                        + (a@[2] as int) * (b@[2] as int) == 0) by (nonlinear_arith)
                        requires
                            b@[0] == -(x1 + x2),
                            b@[1] == x0,
                            b@[2] == x0,
                            a@[0] == x0,
                            a@[1] == x1,
                            a@[2] == x2;
                    assert(Self::abs_sum_prefix(b@, 1)
                        == Self::abs_sum_prefix(b@, 0) + Self::abs_val(b@[0]));
                    assert(Self::abs_sum_prefix(b@, 2)
                        == Self::abs_sum_prefix(b@, 1) + Self::abs_val(b@[1]));
                    assert(Self::abs_sum_prefix(b@, 3)
                        == Self::abs_sum_prefix(b@, 2) + Self::abs_val(b@[2]));
                    assert(Self::abs_sum_prefix(b@, 0) == 0);
                    assert(Self::abs_sum_prefix(b@, 3) <= 40000);
                }
            }

            let mut i: usize = 3;
            while i < n
                invariant
                    n == a.len(),
                    2 <= n <= 100000,
                    n % 2 == 1,
                    3 <= i <= n,
                    i % 2 == 1,
                    b.len() == i,
                    forall|k: int| 0 <= k < a.len() ==> -10000 <= #[trigger] a[k] <= 10000,
                    forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] != 0,
                    b[0] != 0,
                    b[1] != 0,
                    b[2] != 0,
                    (a[0] as int) * (b[0] as int)
                        + (a[1] as int) * (b[1] as int)
                        + (a[2] as int) * (b[2] as int)
                        == 0,
                    Self::abs_sum_prefix(b@, 3) <= 40000,
                    forall|j: int|
                        3 <= j < i as int && (j - 3) % 2 == 0
                            ==> #[trigger] b[j] == a[j + 1],
                    forall|j: int|
                        4 <= j < i as int && (j - 4) % 2 == 0
                            ==> #[trigger] b[j] == -a[j - 1],
                decreases n - i,
            {
                let ghost old_i = i;
                let ghost b_before = b@;
                b.push(a[i + 1]);
                b.push(-a[i]);
                i = i + 2;
                proof {
                    Self::lemma_abs_sum_prefix_append_invariant(b_before, b@, 3);
                    assert(b[old_i as int] == a[old_i as int + 1]);
                    assert(b[old_i as int + 1] == -a[old_i as int]);
                    assert forall|j: int|
                        3 <= j < i as int && (j - 3) % 2 == 0
                            implies #[trigger] b[j] == a[j + 1] by {
                        if j < old_i as int {
                        } else {
                            assert(j == old_i as int);
                        }
                    };
                    assert forall|j: int|
                        4 <= j < i as int && (j - 4) % 2 == 0
                            implies #[trigger] b[j] == -a[j - 1] by {
                        if j < old_i as int {
                        } else {
                            assert(j == old_i as int + 1);
                        }
                    };
                }
            }

            proof {
                assert(b.len() == a.len());
                assert forall|k: int| 0 <= k < a.len() implies b[k] != 0 by {
                    if k < 3 {
                        if k == 0 {
                            assert(b[k] != 0);
                        } else if k == 1 {
                            assert(b[k] != 0);
                        } else {
                            assert(k == 2);
                            assert(b[k] != 0);
                        }
                    } else {
                        if (k - 3) % 2 == 0 {
                            assert(b[k] == a[k + 1]);
                            assert(a[k + 1] != 0);
                        } else {
                            assert(k >= 4);
                            assert((k - 4) % 2 == 0);
                            assert(b[k] == -a[k - 1]);
                            assert(a[k - 1] != 0);
                        }
                    }
                };
                assert forall|j: int|
                    3 <= j < a.len() && (j - 3) % 2 == 0
                        implies (a[j] as int) * (#[trigger] b[j] as int) + (a[j + 1] as int) * (b[j + 1] as int) == 0 by {
                    assert(b[j] == a[j + 1]);
                    assert((j + 1 - 4) % 2 == 0);
                    assert(b[j + 1] == -a[j]);
                    assert((a[j] as int) * (b[j] as int) + (a[j + 1] as int) * (b[j + 1] as int) == 0) by (nonlinear_arith)
                        requires
                            b[j] == a[j + 1],
                            b[j + 1] == -a[j];
                };
                assert(Self::dot_prefix(a@, b@, 3)
                    == Self::dot_prefix(a@, b@, 2) + (a@[2] as int) * (b@[2] as int));
                assert(Self::dot_prefix(a@, b@, 2)
                    == Self::dot_prefix(a@, b@, 1) + (a@[1] as int) * (b@[1] as int));
                assert(Self::dot_prefix(a@, b@, 1)
                    == Self::dot_prefix(a@, b@, 0) + (a@[0] as int) * (b@[0] as int));
                assert(Self::dot_prefix(a@, b@, 0) == 0);
                assert(Self::dot_prefix(a@, b@, 3)
                    == (a@[0] as int) * (b@[0] as int)
                        + (a@[1] as int) * (b@[1] as int)
                        + (a@[2] as int) * (b@[2] as int));
                assert(Self::dot_prefix(a@, b@, 3) == 0);
                Self::lemma_even_pairs_zero(a@, b@, 3, a@.len() as int);
                assert(Self::dot(a@, b@) == Self::dot_prefix(a@, b@, a@.len() as int));
                assert(Self::dot(a@, b@) == 0);
                assert forall|j: int|
                    3 <= j < a.len() && (j - 3) % 2 == 0
                        implies #[trigger] Self::abs_val(b[j]) + Self::abs_val(b[j + 1]) <= 20000 by {
                    assert(b[j] == a[j + 1]);
                    assert((j + 1 - 4) % 2 == 0);
                    assert(b[j + 1] == -a[j]);
                    assert(-10000 <= a[j] as int <= 10000);
                    assert(-10000 <= a[j + 1] as int <= 10000);
                };
                Self::lemma_pair_abs_bound(b@, 3, a@.len() as int);
                assert(Self::abs_sum_prefix(b@, 3) <= 40000);
                assert(n % 2 == 1);
                assert(n <= 99999);
                assert(Self::abs_sum_prefix(b@, a@.len() as int)
                    <= Self::abs_sum_prefix(b@, 3) + 10000 * (a@.len() as int - 3));
                assert(Self::abs_sum_prefix(b@, a@.len() as int) <= 1_000_000_000);
            }
        } else {
            let mut i: usize = 0;
            while i < n
                invariant
                    n == a.len(),
                    2 <= n <= 100000,
                    n % 2 == 0,
                    0 <= i <= n,
                    i % 2 == 0,
                    b.len() == i,
                    forall|k: int| 0 <= k < a.len() ==> -10000 <= #[trigger] a[k] <= 10000,
                    forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] != 0,
                    forall|j: int|
                        0 <= j < i as int && j % 2 == 0
                            ==> #[trigger] b[j] == a[j + 1],
                    forall|j: int|
                        1 <= j < i as int && j % 2 == 1
                            ==> #[trigger] b[j] == -a[j - 1],
                decreases n - i,
            {
                let ghost old_i = i;
                b.push(a[i + 1]);
                b.push(-a[i]);
                i = i + 2;
                proof {
                    assert(b[old_i as int] == a[old_i as int + 1]);
                    assert(b[old_i as int + 1] == -a[old_i as int]);
                    assert forall|j: int|
                        0 <= j < i as int && j % 2 == 0
                            implies #[trigger] b[j] == a[j + 1] by {
                        if j < old_i as int {
                        } else {
                            assert(j == old_i as int);
                        }
                    };
                    assert forall|j: int|
                        1 <= j < i as int && j % 2 == 1
                            implies #[trigger] b[j] == -a[j - 1] by {
                        if j < old_i as int {
                        } else {
                            assert(j == old_i as int + 1);
                        }
                    };
                }
            }

            proof {
                assert(b.len() == a.len());
                assert forall|k: int| 0 <= k < a.len() implies b[k] != 0 by {
                    if k % 2 == 0 {
                        assert(b[k] == a[k + 1]);
                        assert(a[k + 1] != 0);
                    } else {
                        assert(1 <= k);
                        assert(b[k] == -a[k - 1]);
                        assert(a[k - 1] != 0);
                    }
                };
                assert forall|j: int|
                    0 <= j < a.len() && j % 2 == 0
                        implies (a[j] as int) * (#[trigger] b[j] as int) + (a[j + 1] as int) * (b[j + 1] as int) == 0 by {
                    assert(b[j] == a[j + 1]);
                    assert((j + 1) % 2 == 1);
                    assert(b[j + 1] == -a[j]);
                    assert((a[j] as int) * (b[j] as int) + (a[j + 1] as int) * (b[j + 1] as int) == 0) by (nonlinear_arith)
                        requires
                            b[j] == a[j + 1],
                            b[j + 1] == -a[j];
                };
                assert(Self::dot_prefix(a@, b@, 0) == 0);
                Self::lemma_even_pairs_zero(a@, b@, 0, a@.len() as int);
                assert(Self::dot(a@, b@) == Self::dot_prefix(a@, b@, a@.len() as int));
                assert(Self::dot(a@, b@) == 0);
                assert forall|j: int|
                    0 <= j < a.len() && j % 2 == 0
                        implies #[trigger] Self::abs_val(b[j]) + Self::abs_val(b[j + 1]) <= 20000 by {
                    assert(b[j] == a[j + 1]);
                    assert((j + 1) % 2 == 1);
                    assert(b[j + 1] == -a[j]);
                    assert(-10000 <= a[j] as int <= 10000);
                    assert(-10000 <= a[j + 1] as int <= 10000);
                };
                Self::lemma_pair_abs_bound(b@, 0, a@.len() as int);
                assert(Self::abs_sum_prefix(b@, 0) == 0);
                assert(Self::abs_sum_prefix(b@, a@.len() as int)
                    <= Self::abs_sum_prefix(b@, 0) + 10000 * (a@.len() as int - 0));
                assert(n <= 100000);
                assert(Self::abs_sum_prefix(b@, a@.len() as int) <= 1_000_000_000);
            }
        }

        b
    }
}

}
