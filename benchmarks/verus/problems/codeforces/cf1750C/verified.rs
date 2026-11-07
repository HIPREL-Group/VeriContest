use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn xor_val(x: i64, y: i64) -> int {
        if x == y { 0 } else { 1 }
    }

    pub open spec fn spec_flip(v: i64) -> i64 {
        (1 - (v as int)) as i64
    }

    pub open spec fn spec_flip_n(v: i64, n: int) -> i64 {
        if n % 2 == 0 { v } else { Self::spec_flip(v) }
    }

    proof fn lemma_flip_n_add_one(v: i64, n: int)
        requires
            n >= 0,
            v == 0 || v == 1,
        ensures
            Self::spec_flip_n(v, n + 1) == Self::spec_flip(Self::spec_flip_n(v, n)),
    {
        if n % 2 == 0 {
            assert((n + 1) % 2 == 1) by (nonlinear_arith) requires n % 2 == 0;
        } else {
            assert((n + 1) % 2 == 0) by (nonlinear_arith) requires n % 2 == 1;
            assert(Self::spec_flip(Self::spec_flip(v)) == v);
        }
    }

    proof fn lemma_flip_n_same(v: i64, n: int)
        requires
            n % 2 == 0,
        ensures
            Self::spec_flip_n(v, n) == v,
    {
    }

    proof fn lemma_flip_flip(v: i64)
        requires v == 0 || v == 1,
        ensures Self::spec_flip(Self::spec_flip(v)) == v,
    {
    }

    pub open spec fn apply_op(a: Seq<i64>, b: Seq<i64>, lo: int, hi: int) -> (Seq<i64>, Seq<i64>) {
        (
            Seq::new(a.len(), |i: int| if lo <= i <= hi { Self::spec_flip(a[i]) } else { a[i] }),
            Seq::new(b.len(), |i: int| if lo <= i <= hi { b[i] } else { Self::spec_flip(b[i]) }),
        )
    }

    pub open spec fn apply_ops(a: Seq<i64>, b: Seq<i64>, ops: Seq<(int, int)>) -> (Seq<i64>, Seq<i64>)
        decreases ops.len(),
    {
        if ops.len() == 0 {
            (a, b)
        } else {
            let prev = Self::apply_ops(a, b, ops.drop_last());
            Self::apply_op(prev.0, prev.1, ops.last().0, ops.last().1)
        }
    }

    pub open spec fn zero_seq(n: nat) -> Seq<i64> {
        Seq::new(n, |i: int| 0i64)
    }

    pub open spec fn one_seq(n: nat) -> Seq<i64> {
        Seq::new(n, |i: int| 1i64)
    }

    pub open spec fn count_ones(a: Seq<i64>, i: nat) -> int
        decreases i,
    {
        if i == 0 {
            0
        } else {
            Self::count_ones(a, (i - 1) as nat) + (if a[(i - 1) as int] == 1 { 1int } else { 0int })
        }
    }

    pub open spec fn ones_ops(a: Seq<i64>, i: nat) -> Seq<(int, int)>
        decreases i,
    {
        if i == 0 {
            Seq::empty()
        } else {
            let prev = Self::ones_ops(a, (i - 1) as nat);
            if a[(i - 1) as int] == 1 {
                prev.push(((i - 1) as int, (i - 1) as int))
            } else {
                prev
            }
        }
    }

    proof fn lemma_count_ones_nonneg(a: Seq<i64>, i: nat)
        ensures
            Self::count_ones(a, i) >= 0,
        decreases i,
    {
        if i == 0 {
        } else {
            Self::lemma_count_ones_nonneg(a, (i - 1) as nat);
        }
    }

    proof fn lemma_count_ones_monotonic(a: Seq<i64>, i: nat, k: nat)
        requires
            k <= i,
        ensures
            Self::count_ones(a, k) <= Self::count_ones(a, i),
        decreases i,
    {
        if k == i {
        } else {
            Self::lemma_count_ones_monotonic(a, (i - 1) as nat, k);
            Self::lemma_count_ones_nonneg(a, (i - 1) as nat);
        }
    }

    proof fn lemma_count_ones_at_least(a: Seq<i64>, i: nat, j: int)
        requires
            0 <= j < (i as int),
        ensures
            Self::count_ones(a, i) >= (if a[j] == 1 { 1int } else { 0int }),
    {
        Self::lemma_count_ones_nonneg(a, j as nat);
        Self::lemma_count_ones_monotonic(a, i, (j + 1) as nat);
    }

    pub open spec fn phase1_a(a: Seq<i64>, b: Seq<i64>, i: nat) -> Seq<i64> {
        Self::apply_ops(a, b, Self::ones_ops(a, i)).0
    }

    pub open spec fn phase1_b(a: Seq<i64>, b: Seq<i64>, i: nat) -> Seq<i64> {
        Self::apply_ops(a, b, Self::ones_ops(a, i)).1
    }

    proof fn lemma_phase1_state(a: Seq<i64>, b: Seq<i64>, i: nat)
        requires
            a.len() == b.len(),
            (i as int) <= a.len(),
            forall|j: int| 0 <= j < a.len() ==> (#[trigger] a[j] == 0 || a[j] == 1),
            forall|j: int| 0 <= j < b.len() ==> (#[trigger] b[j] == 0 || b[j] == 1),
        ensures
            Self::phase1_a(a, b, i).len() == a.len(),
            Self::phase1_b(a, b, i).len() == b.len(),
            forall|j: int| 0 <= j < (i as int) ==> #[trigger] Self::phase1_a(a, b, i)[j] == 0,
            forall|j: int| (i as int) <= j < a.len() ==> #[trigger] Self::phase1_a(a, b, i)[j] == a[j],
            forall|j: int| 0 <= j < (i as int) ==> #[trigger] Self::phase1_b(a, b, i)[j] ==
                Self::spec_flip_n(b[j], Self::count_ones(a, i) - (if a[j] == 1 { 1int } else { 0int })),
            forall|j: int| (i as int) <= j < a.len() ==> #[trigger] Self::phase1_b(a, b, i)[j] ==
                Self::spec_flip_n(b[j], Self::count_ones(a, i) as int),
        decreases i,
    {
        if i == 0 {
            assert(Self::ones_ops(a, 0) =~= Seq::<(int, int)>::empty());
            assert(Self::apply_ops(a, b, Seq::<(int, int)>::empty()) == (a, b));
            assert forall|j: int| 0 <= j < a.len() implies #[trigger] Self::phase1_b(a, b, 0)[j] ==
                Self::spec_flip_n(b[j], Self::count_ones(a, 0) as int) by {
                Self::lemma_flip_n_same(b[j], 0);
            }
        } else {
            let im1: nat = (i - 1) as nat;
            let j0: int = (i - 1) as int;
            Self::lemma_phase1_state(a, b, im1);
            let prev_a = Self::phase1_a(a, b, im1);
            let prev_b = Self::phase1_b(a, b, im1);
            let prev_ops = Self::ones_ops(a, im1);
            if a[j0] == 1 {
                assert(Self::ones_ops(a, i) =~= prev_ops.push((j0, j0)));
                assert(prev_ops.push((j0, j0)).drop_last() == prev_ops);
                assert(prev_ops.push((j0, j0)).last() == (j0, j0));
                assert(Self::apply_ops(a, b, prev_ops.push((j0, j0)))
                    == Self::apply_op(prev_a, prev_b, j0, j0));
                let new_a = Self::apply_op(prev_a, prev_b, j0, j0).0;
                let new_b = Self::apply_op(prev_a, prev_b, j0, j0).1;
                assert(Self::phase1_a(a, b, i) =~= new_a);
                assert(Self::phase1_b(a, b, i) =~= new_b);
                assert(Self::count_ones(a, i) == Self::count_ones(a, im1) + 1);
                assert forall|j: int| 0 <= j < a.len() implies #[trigger] new_b[j] ==
                    (if j == j0 { prev_b[j] } else { Self::spec_flip(prev_b[j]) }) by {}
                assert forall|j: int| 0 <= j < a.len() implies #[trigger] new_a[j] ==
                    (if j == j0 { Self::spec_flip(prev_a[j]) } else { prev_a[j] }) by {}
                assert forall|j: int| 0 <= j < (i as int) implies #[trigger] Self::phase1_a(a, b, i)[j] == 0 by {
                    if j == j0 {
                        assert(Self::phase1_a(a, b, i)[j] == Self::spec_flip(prev_a[j]));
                        assert(prev_a[j] == a[j0]);
                    }
                }
                assert forall|j: int| (i as int) <= j < a.len() implies #[trigger] Self::phase1_a(a, b, i)[j] == a[j] by {}
                Self::lemma_count_ones_nonneg(a, im1);
                assert forall|j: int| 0 <= j < (i as int) implies #[trigger] Self::phase1_b(a, b, i)[j] ==
                    Self::spec_flip_n(b[j], Self::count_ones(a, i) - (if a[j] == 1 { 1int } else { 0int })) by {
                    if j == j0 {
                        assert(Self::phase1_b(a, b, i)[j] == prev_b[j]);
                        assert(prev_b[j] == Self::spec_flip_n(b[j], Self::count_ones(a, im1) as int));
                        assert(Self::count_ones(a, i) - 1 == Self::count_ones(a, im1));
                    } else {
                        Self::lemma_count_ones_at_least(a, im1, j);
                        Self::lemma_flip_n_add_one(b[j], Self::count_ones(a, im1) - (if a[j] == 1 { 1int } else { 0int }));
                    }
                }
                assert forall|j: int| (i as int) <= j < a.len() implies #[trigger] Self::phase1_b(a, b, i)[j] ==
                    Self::spec_flip_n(b[j], Self::count_ones(a, i) as int) by {
                    Self::lemma_flip_n_add_one(b[j], Self::count_ones(a, im1) as int);
                }
            } else {
                assert(Self::ones_ops(a, i) =~= prev_ops);
                assert(Self::count_ones(a, i) == Self::count_ones(a, im1));
            }
        }
    }

    proof fn lemma_b2_const_helper(c: i64, m: int)
        requires
            m >= 1,
            c == 0 || c == 1,
        ensures
            Self::spec_flip_n(Self::spec_flip(c), m - 1) == Self::spec_flip_n(c, m),
    {
        if m % 2 == 0 {
            assert((m - 1) % 2 == 1) by (nonlinear_arith) requires m % 2 == 0;
            Self::lemma_flip_flip(c);
        } else {
            assert((m - 1) % 2 == 0) by (nonlinear_arith) requires m % 2 == 1;
        }
    }

    proof fn lemma_phase1_final(a: Seq<i64>, b: Seq<i64>)
        requires
            a.len() == b.len(),
            a.len() >= 1,
            forall|j: int| 0 <= j < a.len() ==> (#[trigger] a[j] == 0 || a[j] == 1),
            forall|j: int| 0 <= j < b.len() ==> (#[trigger] b[j] == 0 || b[j] == 1),
            forall|j: int| 0 <= j < a.len() ==> Self::xor_val(#[trigger] a[j], b[j]) == Self::xor_val(a[0], b[0]),
        ensures
            ({
                let n = a.len() as nat;
                let c = if a[0] == b[0] { 0i64 } else { 1i64 };
                let total = Self::count_ones(a, n);
                &&& Self::phase1_a(a, b, n).len() == a.len()
                &&& Self::phase1_b(a, b, n).len() == b.len()
                &&& forall|j: int| 0 <= j < a.len() ==> #[trigger] Self::phase1_a(a, b, n)[j] == 0
                &&& forall|j: int| 0 <= j < a.len() ==> #[trigger] Self::phase1_b(a, b, n)[j] ==
                        Self::spec_flip_n(c, total)
            }),
    {
        let n = a.len() as nat;
        Self::lemma_phase1_state(a, b, n);
        let c: i64 = if a[0] == b[0] { 0i64 } else { 1i64 };
        let total = Self::count_ones(a, n);
        Self::lemma_count_ones_nonneg(a, n);
        assert forall|j: int| 0 <= j < a.len() implies #[trigger] Self::phase1_b(a, b, n)[j] ==
            Self::spec_flip_n(c, total) by {
            if a[j] == 1 {
                assert(b[j] == Self::spec_flip(c));
                assert(Self::phase1_b(a, b, n)[j] ==
                    Self::spec_flip_n(b[j], total - 1));
                Self::lemma_count_ones_at_least(a, n, j);
                Self::lemma_b2_const_helper(c, total);
            } else {
                assert(b[j] == c);
                assert(Self::phase1_b(a, b, n)[j] == Self::spec_flip_n(b[j], total));
            }
        }
    }

    proof fn lemma_phase2_fixup(n: nat)
        requires
            n >= 2,
        ensures
            Self::apply_ops(
                Self::zero_seq(n),
                Self::one_seq(n),
                seq![(0int, 0int), (1int, (n - 1) as int), (0int, (n - 1) as int)],
            ) == (Self::zero_seq(n), Self::zero_seq(n)),
    {
        let a0 = Self::zero_seq(n);
        let b0 = Self::one_seq(n);
        let ops = seq![(0int, 0int), (1int, (n - 1) as int), (0int, (n - 1) as int)];
        let s1 = Self::apply_op(a0, b0, 0, 0);
        let s2 = Self::apply_op(s1.0, s1.1, 1, (n - 1) as int);
        let s3 = Self::apply_op(s2.0, s2.1, 0, (n - 1) as int);
        assert(ops.drop_last() == seq![(0int, 0int), (1int, (n - 1) as int)]);
        assert(ops.last() == (0int, (n - 1) as int));
        assert(ops.drop_last().drop_last() == seq![(0int, 0int)]);
        assert(ops.drop_last().last() == (1int, (n - 1) as int));
        assert(seq![(0int, 0int)].drop_last() == Seq::<(int, int)>::empty());
        assert(seq![(0int, 0int)].last() == (0int, 0int));
        assert(Self::apply_ops(a0, b0, Seq::<(int, int)>::empty()) == (a0, b0));
        assert(Self::apply_ops(a0, b0, seq![(0int, 0int)]) == s1);
        assert(Self::apply_ops(a0, b0, ops.drop_last()) == s2);
        assert(Self::apply_ops(a0, b0, ops) == s3);
        assert(s3.0 =~= Self::zero_seq(n));
        assert(s3.1 =~= Self::zero_seq(n));
    }

    proof fn lemma_apply_ops_concat(a: Seq<i64>, b: Seq<i64>, x: Seq<(int, int)>, y: Seq<(int, int)>)
        ensures
            Self::apply_ops(a, b, x + y) ==
                Self::apply_ops(Self::apply_ops(a, b, x).0, Self::apply_ops(a, b, x).1, y),
        decreases y.len(),
    {
        if y.len() == 0 {
            assert((x + y) =~= x);
        } else {
            assert((x + y).drop_last() =~= x + y.drop_last());
            assert((x + y).last() == y.last());
            Self::lemma_apply_ops_concat(a, b, x, y.drop_last());
        }
    }

    pub open spec fn to_int_ops(ops: Seq<(usize, usize)>) -> Seq<(int, int)> {
        Seq::new(ops.len(), |k: int| ((ops[k].0 - 1) as int, (ops[k].1 - 1) as int))
    }

    proof fn lemma_ones_ops_len(a: Seq<i64>, i: nat)
        ensures
            Self::ones_ops(a, i).len() as int == Self::count_ones(a, i),
        decreases i,
    {
        if i == 0 {
        } else {
            Self::lemma_ones_ops_len(a, (i - 1) as nat);
        }
    }

    proof fn lemma_count_ones_le(a: Seq<i64>, i: nat)
        ensures
            Self::count_ones(a, i) <= (i as int),
        decreases i,
    {
        if i == 0 {
        } else {
            Self::lemma_count_ones_le(a, (i - 1) as nat);
        }
    }

    pub fn complementary_xor_ops(a: Vec<i64>, b: Vec<i64>) -> (result: (bool, Vec<(usize, usize)>))
        requires
            a.len() == b.len(),
            2 <= a.len() && a.len() <= 200_000,
            forall|i: int| 0 <= i < a.len() ==> (#[trigger] a@[i] == 0 || a@[i] == 1),
            forall|i: int| 0 <= i < b.len() ==> (#[trigger] b@[i] == 0 || b@[i] == 1),
        ensures
            result.0 == (forall|i: int| 0 <= i < a@.len() ==>
                Self::xor_val(#[trigger] a@[i], b@[i]) == Self::xor_val(a@[0], b@[0])),
            !result.0 ==> result.1.len() == 0,
            result.0 ==> {
                &&& result.1.len() <= a.len() + 5
                &&& forall|j: int| 0 <= j < result.1@.len() ==>
                        1 <= #[trigger] result.1@[j].0 <= result.1@[j].1 <= a.len()
                &&& Self::apply_ops(a@, b@, Self::to_int_ops(result.1@))
                        == (Self::zero_seq(a.len() as nat), Self::zero_seq(a.len() as nat))
            },
    {
        let n = a.len();
        let first_xor = if a[0] == b[0] { 0i64 } else { 1i64 };
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                n == a.len(),
                n == b.len(),
                n >= 2,
                forall|j: int| 0 <= j < a.len() ==> (#[trigger] a@[j] == 0 || a@[j] == 1),
                forall|j: int| 0 <= j < b.len() ==> (#[trigger] b@[j] == 0 || b@[j] == 1),
                first_xor as int == Self::xor_val(a@[0], b@[0]),
                forall|j: int| 0 <= j < i as int ==>
                    Self::xor_val(#[trigger] a@[j], b@[j]) == Self::xor_val(a@[0], b@[0]),
            decreases n - i,
        {
            let cur_xor = if a[i] == b[i] { 0i64 } else { 1i64 };
            if cur_xor != first_xor {
                proof {
                    assert(Self::xor_val(a@[i as int], b@[i as int]) != Self::xor_val(a@[0], b@[0]));
                }
                return (false, Vec::new());
            }
            proof {
                assert(Self::xor_val(a@[i as int], b@[i as int]) == Self::xor_val(a@[0], b@[0]));
            }
            i = i + 1;
        }
        let mut ops: Vec<(usize, usize)> = Vec::with_capacity(n + 3);
        let mut ones: usize = 0;
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == a.len(),
                n == b.len(),
                n >= 2,
                forall|k: int| 0 <= k < a.len() ==> (#[trigger] a@[k] == 0 || a@[k] == 1),
                forall|k: int| 0 <= k < b.len() ==> (#[trigger] b@[k] == 0 || b@[k] == 1),
                ones as int == Self::count_ones(a@, j as nat),
                ones <= j,
                Self::to_int_ops(ops@) == Self::ones_ops(a@, j as nat),
                forall|k: int| 0 <= k < ops@.len() ==> 1 <= #[trigger] ops@[k].0 <= ops@[k].1 <= n,
            decreases n - j,
        {
            proof {
                Self::lemma_ones_ops_len(a@, j as nat);
                Self::lemma_count_ones_nonneg(a@, j as nat);
            }
            if a[j] == 1 {
                let ghost prev_ops_seq = ops@;
                ones = ones + 1;
                ops.push((j + 1, j + 1));
                proof {
                    assert(Self::ones_ops(a@, (j + 1) as nat) =~= Self::ones_ops(a@, j as nat).push((j as int, j as int)));
                    assert(Self::to_int_ops(ops@) =~= Self::to_int_ops(prev_ops_seq).push((j as int, j as int)));
                }
            } else {
                proof {
                    assert(Self::ones_ops(a@, (j + 1) as nat) =~= Self::ones_ops(a@, j as nat));
                }
            }
            j = j + 1;
        }
        proof {
            Self::lemma_phase1_final(a@, b@);
        }
        let parity = (ones % 2) as i64;
        if parity != first_xor {
            let ghost prev_ops_seq2 = ops@;
            ops.push((1, 1));
            ops.push((2, n));
            ops.push((1, n));
            proof {
                let c: i64 = first_xor;
                let total = Self::count_ones(a@, n as nat);
                assert forall|k: int| 0 <= k < a.len() implies #[trigger] Self::phase1_b(a@, b@, n as nat)[k] == 1i64 by {
                    if total % 2 == 0 {
                        assert(c == 1);
                    } else {
                        assert(c == 0);
                    }
                }
                assert(Self::phase1_b(a@, b@, n as nat) =~= Self::one_seq(n as nat));
                assert(Self::phase1_a(a@, b@, n as nat) =~= Self::zero_seq(n as nat));
                Self::lemma_phase2_fixup(n as nat);
                let fixup = seq![(0int, 0int), (1int, (n - 1) as int), (0int, (n - 1) as int)];
                Self::lemma_apply_ops_concat(a@, b@, Self::ones_ops(a@, n as nat), fixup);
                assert(Self::to_int_ops(ops@) =~= Self::to_int_ops(prev_ops_seq2) + fixup);
                assert(Self::apply_ops(a@, b@, Self::to_int_ops(ops@))
                    == (Self::zero_seq(n as nat), Self::zero_seq(n as nat)));
                Self::lemma_ones_ops_len(a@, n as nat);
                Self::lemma_count_ones_le(a@, n as nat);
                assert(ops@.len() <= a.len() + 5);
                assert forall|k: int| 0 <= k < ops@.len() implies
                    1 <= #[trigger] ops@[k].0 <= ops@[k].1 <= a.len() by {}
            }
        } else {
            proof {
                let c: i64 = first_xor;
                let total = Self::count_ones(a@, n as nat);
                assert forall|k: int| 0 <= k < a.len() implies #[trigger] Self::phase1_b(a@, b@, n as nat)[k] == 0i64 by {
                    if total % 2 == 0 {
                        assert(c == 0);
                    } else {
                        assert(c == 1);
                    }
                }
                assert(Self::phase1_b(a@, b@, n as nat) =~= Self::zero_seq(n as nat));
                assert(Self::phase1_a(a@, b@, n as nat) =~= Self::zero_seq(n as nat));
                assert(Self::apply_ops(a@, b@, Self::to_int_ops(ops@))
                    == (Self::zero_seq(n as nat), Self::zero_seq(n as nat)));
                Self::lemma_ones_ops_len(a@, n as nat);
                Self::lemma_count_ones_le(a@, n as nat);
                assert(ops@.len() <= a.len() + 5);
            }
        }
        (true, ops)
    }
}

}
