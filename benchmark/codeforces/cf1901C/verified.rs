use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn halving_steps(d: int) -> int
    decreases d
{
    if d <= 0 { 0 } else { 1 + halving_steps(d / 2) }
}

proof fn lemma_halving_steps_nonneg(d: int)
    ensures
        halving_steps(d) >= 0,
    decreases d,
{
    if d <= 0 {
    } else {
        lemma_halving_steps_nonneg(d / 2);
    }
}

pub open spec fn is_min_max_of(a: Seq<i64>, mn: int, mx: int) -> bool {
    a.len() >= 1
    && (forall|i: int| 0 <= i < a.len() ==> mn <= #[trigger] (a[i] as int) <= mx)
    && (exists|i: int| 0 <= i < a.len() && a[i] as int == mn)
    && (exists|i: int| 0 <= i < a.len() && a[i] as int == mx)
}

pub struct Solution;

impl Solution {
    pub fn steps_from_diff(d: i64) -> (res: i64)
        requires
            d >= 0,
        ensures
            res >= 0,
            res <= d,
            res as int == halving_steps(d as int),
        decreases d,
    {
        if d == 0 {
            0
        } else {
            let sub = Self::steps_from_diff(d / 2);
            proof {
                assert(d / 2 + 1 <= d);
            }
            sub + 1
        }
    }

    pub fn min_operations(a: Vec<i64>) -> (result: i64)
        requires
            1 <= a.len() <= 200_000,
            forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] <= 1_000_000_000,
        ensures
            result >= 0,
            exists|mn: int, mx: int|
                is_min_max_of(a@, mn, mx)
                && result as int == halving_steps(mx - mn),
    {
        let n = a.len();
        let mut mn = a[0];
        let mut mx = a[0];
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                n == a.len(),
                forall|j: int| 0 <= j < n ==> 0 <= #[trigger] a[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> mn <= #[trigger] a[j],
                forall|j: int| 0 <= j < i ==> #[trigger] a[j] <= mx,
                exists|j: int| 0 <= j < i && a[j] == mn,
                exists|j: int| 0 <= j < i && a[j] == mx,
            decreases n - i,
        {
            let cur = a[i];
            if cur < mn {
                mn = cur;
            }
            if cur > mx {
                mx = cur;
            }
            i += 1;
        }
        let result = Self::steps_from_diff(mx - mn);
        proof {
            assert(i == n);
            assert(is_min_max_of(a@, mn as int, mx as int));
            assert(exists|mn0: int, mx0: int|
                is_min_max_of(a@, mn0, mx0)
                && result as int == halving_steps(mx0 - mn0)) by {
                let mn0 = mn as int;
                let mx0 = mx as int;
                assert(is_min_max_of(a@, mn0, mx0));
                assert(result as int == halving_steps((mx - mn) as int));
                assert((mx - mn) as int == mx0 - mn0);
            }
        }

        Self::steps_from_diff(mx - mn)
    }

    pub open spec fn apply_x(v: int, x: int) -> int {
        (v + x) / 2
    }

    proof fn lemma_apply_x_mono(u: int, w: int, x: int)
        requires
            0 <= u <= w,
            0 <= x,
        ensures
            0 <= Self::apply_x(u, x) <= Self::apply_x(w, x),
    {
        assert(Self::apply_x(u, x) <= Self::apply_x(w, x)) by (nonlinear_arith)
            requires 0 <= u <= w, 0 <= x;
        assert(0 <= Self::apply_x(u, x)) by (nonlinear_arith)
            requires 0 <= u, 0 <= x;
    }

    pub open spec fn opt_x(mn: int, mx: int) -> int {
        if mn % 2 == 1 && mx % 2 == 0 { 1 } else { 0 }
    }

    pub open spec fn step_state(mn: int, mx: int, t: nat) -> (int, int)
        decreases t,
    {
        if t == 0 {
            (mn, mx)
        } else {
            let prev = Self::step_state(mn, mx, (t - 1) as nat);
            let x = Self::opt_x(prev.0, prev.1);
            (Self::apply_x(prev.0, x), Self::apply_x(prev.1, x))
        }
    }

    proof fn lemma_step_gap(mn: int, mx: int)
        requires
            0 <= mn <= mx,
        ensures
            ({
                let x = Self::opt_x(mn, mx);
                Self::apply_x(mx, x) - Self::apply_x(mn, x) == (mx - mn) / 2
            }),
    {
        let d = mx - mn;
        if mn % 2 == 0 && mx % 2 == 0 {
            assert(Self::opt_x(mn, mx) == 0);
            assert(mx / 2 - mn / 2 == d / 2) by (nonlinear_arith) requires mn % 2 == 0, mx % 2 == 0, mx - mn == d;
        } else if mn % 2 == 0 && mx % 2 == 1 {
            assert(Self::opt_x(mn, mx) == 0);
            assert(mx / 2 - mn / 2 == d / 2) by (nonlinear_arith) requires mn % 2 == 0, mx % 2 == 1, mx - mn == d;
        } else if mn % 2 == 1 && mx % 2 == 0 {
            assert(Self::opt_x(mn, mx) == 1);
            assert((mx + 1) / 2 - (mn + 1) / 2 == d / 2) by (nonlinear_arith)
                requires mn % 2 == 1, mx % 2 == 0, mx - mn == d;
        } else {
            assert(Self::opt_x(mn, mx) == 0);
            assert(mx / 2 - mn / 2 == d / 2) by (nonlinear_arith) requires mn % 2 == 1, mx % 2 == 1, mx - mn == d;
        }
    }

    pub open spec fn one_step(mn: int, mx: int) -> (int, int) {
        let x = Self::opt_x(mn, mx);
        (Self::apply_x(mn, x), Self::apply_x(mx, x))
    }

    proof fn lemma_step_state_front(mn: int, mx: int, t: nat)
        ensures
            ({
                let s = Self::one_step(mn, mx);
                Self::step_state(mn, mx, (t + 1) as nat) == Self::step_state(s.0, s.1, t)
            }),
        decreases t,
    {
        let s = Self::one_step(mn, mx);
        if t == 0 {
            assert(Self::step_state(mn, mx, 1) == {
                let prev = Self::step_state(mn, mx, 0);
                let x = Self::opt_x(prev.0, prev.1);
                (Self::apply_x(prev.0, x), Self::apply_x(prev.1, x))
            });
        } else {
            Self::lemma_step_state_front(mn, mx, (t - 1) as nat);
            assert(Self::step_state(mn, mx, (t + 1) as nat) == {
                let prev = Self::step_state(mn, mx, t);
                let x = Self::opt_x(prev.0, prev.1);
                (Self::apply_x(prev.0, x), Self::apply_x(prev.1, x))
            });
            assert(Self::step_state(s.0, s.1, t) == {
                let prev = Self::step_state(s.0, s.1, (t - 1) as nat);
                let x = Self::opt_x(prev.0, prev.1);
                (Self::apply_x(prev.0, x), Self::apply_x(prev.1, x))
            });
        }
    }

    proof fn lemma_step_state_nonneg(mn: int, mx: int, t: nat)
        requires
            0 <= mn <= mx,
        ensures
            ({
                let s = Self::step_state(mn, mx, t);
                0 <= s.0 <= s.1
            }),
        decreases t,
    {
        if t == 0 {
        } else {
            Self::lemma_step_state_nonneg(mn, mx, (t - 1) as nat);
            let prev = Self::step_state(mn, mx, (t - 1) as nat);
            Self::lemma_apply_x_mono(prev.0, prev.1, Self::opt_x(prev.0, prev.1));
        }
    }

    proof fn lemma_convergence(mn: int, mx: int)
        requires
            0 <= mn <= mx,
        ensures
            ({
                let k = halving_steps(mx - mn);
                let s = Self::step_state(mn, mx, k as nat);
                s.0 == s.1
            }),
        decreases mx - mn,
    {
        let d = mx - mn;
        if d <= 0 {
        } else {
            let k = halving_steps(d);
            let s1 = Self::one_step(mn, mx);
            Self::lemma_step_gap(mn, mx);
            assert(s1.1 - s1.0 == d / 2);
            lemma_halving_steps_nonneg(d / 2);
            assert(k == 1 + halving_steps(d / 2));
            Self::lemma_apply_x_mono(mn, mx, Self::opt_x(mn, mx));
            assert(0 <= s1.0 <= s1.1);
            Self::lemma_convergence(s1.0, s1.1);
            assert(k - 1 == halving_steps(s1.1 - s1.0));
            let km1: nat = (k - 1) as nat;
            assert(km1 as int + 1 == k);
            Self::lemma_step_state_front(mn, mx, km1);
            assert((km1 + 1) as nat == k as nat);
            assert(Self::step_state(mn, mx, k as nat)
                == Self::step_state(s1.0, s1.1, km1));
            assert(km1 == halving_steps(s1.1 - s1.0) as nat);
        }
    }

    pub open spec fn ops_seq(mn: int, mx: int, t: nat) -> Seq<int>
        decreases t,
    {
        if t == 0 {
            Seq::empty()
        } else {
            let prev = Self::step_state(mn, mx, (t - 1) as nat);
            let x = Self::opt_x(prev.0, prev.1);
            Self::ops_seq(mn, mx, (t - 1) as nat).push(x)
        }
    }

    proof fn lemma_ops_seq_len(mn: int, mx: int, t: nat)
        ensures
            Self::ops_seq(mn, mx, t).len() == t,
        decreases t,
    {
        if t == 0 {
        } else {
            Self::lemma_ops_seq_len(mn, mx, (t - 1) as nat);
        }
    }

    pub open spec fn apply_x_scalar_seq(v: int, ops: Seq<int>) -> int
        decreases ops.len(),
    {
        if ops.len() == 0 {
            v
        } else {
            Self::apply_x(Self::apply_x_scalar_seq(v, ops.drop_last()), ops.last())
        }
    }

    proof fn lemma_sandwich(mn: int, mx: int, v: int, t: nat)
        requires
            0 <= mn <= v <= mx,
        ensures
            ({
                let s = Self::step_state(mn, mx, t);
                let r = Self::apply_x_scalar_seq(v, Self::ops_seq(mn, mx, t));
                s.0 <= r <= s.1
            }),
        decreases t,
    {
        if t == 0 {
        } else {
            let tm1: nat = (t - 1) as nat;
            Self::lemma_sandwich(mn, mx, v, tm1);
            Self::lemma_step_state_nonneg(mn, mx, tm1);
            let prev_s = Self::step_state(mn, mx, tm1);
            let prev_r = Self::apply_x_scalar_seq(v, Self::ops_seq(mn, mx, tm1));
            assert(prev_s.0 <= prev_r <= prev_s.1);
            assert(0 <= prev_s.0);
            let x = Self::opt_x(prev_s.0, prev_s.1);
            Self::lemma_ops_seq_len(mn, mx, t);
            assert(Self::ops_seq(mn, mx, t) =~= Self::ops_seq(mn, mx, tm1).push(x));
            assert(Self::ops_seq(mn, mx, t).drop_last() == Self::ops_seq(mn, mx, tm1));
            assert(Self::ops_seq(mn, mx, t).last() == x);
            assert(Self::apply_x_scalar_seq(v, Self::ops_seq(mn, mx, t))
                == Self::apply_x(prev_r, x));
            assert(Self::step_state(mn, mx, t)
                == (Self::apply_x(prev_s.0, x), Self::apply_x(prev_s.1, x)));
            Self::lemma_apply_x_mono(prev_s.0, prev_r, x);
            Self::lemma_apply_x_mono(prev_r, prev_s.1, x);
        }
    }

    proof fn lemma_ops_seq_bound(mn: int, mx: int, t: nat)
        ensures
            forall|k: int| 0 <= k < Self::ops_seq(mn, mx, t).len() ==>
                0 <= #[trigger] Self::ops_seq(mn, mx, t)[k] <= 1,
        decreases t,
    {
        if t == 0 {
        } else {
            Self::lemma_ops_seq_bound(mn, mx, (t - 1) as nat);
            Self::lemma_ops_seq_len(mn, mx, (t - 1) as nat);
            let prev = Self::step_state(mn, mx, (t - 1) as nat);
            let x = Self::opt_x(prev.0, prev.1);
            assert(Self::ops_seq(mn, mx, t) =~= Self::ops_seq(mn, mx, (t - 1) as nat).push(x));
        }
    }

    pub open spec fn apply_x_i64(v: i64, x: i64) -> i64 {
        ((v as int + x as int) / 2) as i64
    }

    pub open spec fn apply_x_seq(a: Seq<i64>, ops: Seq<i64>) -> Seq<i64>
        decreases ops.len(),
    {
        if ops.len() == 0 {
            a
        } else {
            let prev = Self::apply_x_seq(a, ops.drop_last());
            Seq::new(prev.len(), |i: int| Self::apply_x_i64(prev[i], ops.last()))
        }
    }

    pub open spec fn all_equal(a: Seq<i64>) -> bool {
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j]
    }

    pub open spec fn spec_seq_min(a: Seq<i64>) -> i64
        decreases a.len(),
    {
        if a.len() <= 1 {
            a[0]
        } else {
            let sub = Self::spec_seq_min(a.drop_last());
            if a.last() < sub { a.last() } else { sub }
        }
    }

    pub open spec fn spec_seq_max(a: Seq<i64>) -> i64
        decreases a.len(),
    {
        if a.len() <= 1 {
            a[0]
        } else {
            let sub = Self::spec_seq_max(a.drop_last());
            if a.last() > sub { a.last() } else { sub }
        }
    }

    proof fn lemma_seq_min_step(a: Seq<i64>, k: int)
        requires
            1 <= k < a.len(),
        ensures
            Self::spec_seq_min(a.subrange(0, (k + 1) as int)) ==
                if a[k] < Self::spec_seq_min(a.subrange(0, k)) {
                    a[k]
                } else {
                    Self::spec_seq_min(a.subrange(0, k))
                },
    {
        assert(a.subrange(0, (k + 1) as int).drop_last() =~= a.subrange(0, k));
        assert(a.subrange(0, (k + 1) as int).last() == a[k]);
    }

    proof fn lemma_seq_max_step(a: Seq<i64>, k: int)
        requires
            1 <= k < a.len(),
        ensures
            Self::spec_seq_max(a.subrange(0, (k + 1) as int)) ==
                if a[k] > Self::spec_seq_max(a.subrange(0, k)) {
                    a[k]
                } else {
                    Self::spec_seq_max(a.subrange(0, k))
                },
    {
        assert(a.subrange(0, (k + 1) as int).drop_last() =~= a.subrange(0, k));
        assert(a.subrange(0, (k + 1) as int).last() == a[k]);
    }

    proof fn lemma_seq_min_max_bound(a: Seq<i64>)
        requires
            a.len() >= 1,
        ensures
            forall|i: int| 0 <= i < a.len() ==>
                Self::spec_seq_min(a) <= #[trigger] a[i] <= Self::spec_seq_max(a),
        decreases a.len(),
    {
        if a.len() <= 1 {
            assert(Self::spec_seq_min(a) == a[0]);
            assert(Self::spec_seq_max(a) == a[0]);
        } else {
            Self::lemma_seq_min_max_bound(a.drop_last());
            assert(Self::spec_seq_min(a) == if a.last() < Self::spec_seq_min(a.drop_last()) {
                a.last()
            } else {
                Self::spec_seq_min(a.drop_last())
            });
            assert(Self::spec_seq_max(a) == if a.last() > Self::spec_seq_max(a.drop_last()) {
                a.last()
            } else {
                Self::spec_seq_max(a.drop_last())
            });
            assert forall|i: int| 0 <= i < a.len() implies
                Self::spec_seq_min(a) <= #[trigger] a[i] <= Self::spec_seq_max(a) by {
                if i < a.len() - 1 {
                    assert(a[i] == a.drop_last()[i]);
                }
            }
        }
    }

    proof fn lemma_apply_x_scalar_seq_bound(v: int, ops: Seq<int>)
        requires
            v >= 0,
            forall|k: int| 0 <= k < ops.len() ==> 0 <= #[trigger] ops[k] <= 1,
        ensures
            0 <= Self::apply_x_scalar_seq(v, ops) <= v,
        decreases ops.len(),
    {
        if ops.len() == 0 {
        } else {
            Self::lemma_apply_x_scalar_seq_bound(v, ops.drop_last());
            let prev = Self::apply_x_scalar_seq(v, ops.drop_last());
            let x = ops.last();
            assert(0 <= x <= 1);
            assert(Self::apply_x(prev, x) <= prev) by (nonlinear_arith) requires 0 <= prev, 0 <= x <= 1;
            assert(0 <= Self::apply_x(prev, x)) by (nonlinear_arith) requires 0 <= prev, 0 <= x <= 1;
        }
    }

    proof fn lemma_apply_x_seq_len(a: Seq<i64>, ops: Seq<i64>)
        ensures
            Self::apply_x_seq(a, ops).len() == a.len(),
        decreases ops.len(),
    {
        if ops.len() == 0 {
        } else {
            Self::lemma_apply_x_seq_len(a, ops.drop_last());
        }
    }

    proof fn lemma_apply_x_seq_pointwise(a: Seq<i64>, ops: Seq<int>, i: int)
        requires
            0 <= i < a.len(),
            0 <= a[i] as int <= 2_000_000_000,
            forall|k: int| 0 <= k < ops.len() ==> 0 <= #[trigger] ops[k] <= 1,
        ensures
            Self::apply_x_seq(a, Seq::new(ops.len(), |k: int| ops[k] as i64))[i]
                == Self::apply_x_scalar_seq(a[i] as int, ops) as i64,
        decreases ops.len(),
    {
        let ops64 = Seq::new(ops.len(), |k: int| ops[k] as i64);
        if ops.len() == 0 {
        } else {
            Self::lemma_apply_x_seq_pointwise(a, ops.drop_last(), i);
            Self::lemma_apply_x_scalar_seq_bound(a[i] as int, ops.drop_last());
            let ops64_prev = Seq::new(ops.drop_last().len(), |k: int| ops.drop_last()[k] as i64);
            assert(ops64.drop_last() =~= ops64_prev);
            assert(0 <= ops.last() <= 1);
            assert(ops64.last() as int == ops.last());
            Self::lemma_apply_x_seq_len(a, ops64_prev);
            assert(Self::apply_x_seq(a, ops64)
                == {
                    let prev = Self::apply_x_seq(a, ops64.drop_last());
                    Seq::new(prev.len(), |k: int| Self::apply_x_i64(prev[k], ops64.last()))
                });
            assert(Self::apply_x_seq(a, ops64)[i]
                == Self::apply_x_i64(Self::apply_x_seq(a, ops64_prev)[i], ops64.last()));
            assert(Self::apply_x_scalar_seq(a[i] as int, ops)
                == Self::apply_x(Self::apply_x_scalar_seq(a[i] as int, ops.drop_last()), ops.last()));
        }
    }

    pub fn build_operations(a: Vec<i64>) -> (result: Vec<i64>)
        requires
            1 <= a.len() <= 200_000,
            forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] <= 1_000_000_000,
        ensures
            result.len() as int
                == halving_steps(Self::spec_seq_max(a@) as int - Self::spec_seq_min(a@) as int),
            forall|k: int| 0 <= k < result.len() ==>
                0 <= #[trigger] result[k] <= 1_000_000_000_000_000_000,
            Self::all_equal(Self::apply_x_seq(a@, result@)),
    {
        let n = a.len();
        let mut mn = a[0];
        let mut mx = a[0];
        let mut idx: usize = 1;
        proof {
            assert(a@.subrange(0, 1) =~= seq![a@[0]]);
        }
        while idx < n
            invariant
                1 <= idx <= n,
                n == a.len(),
                forall|k: int| 0 <= k < a.len() ==> 0 <= #[trigger] a@[k] <= 1_000_000_000,
                0 <= mn <= mx <= 1_000_000_000,
                mn as int == Self::spec_seq_min(a@.subrange(0, idx as int)),
                mx as int == Self::spec_seq_max(a@.subrange(0, idx as int)),
            decreases n - idx,
        {
            let cur = a[idx];
            proof {
                Self::lemma_seq_min_step(a@, idx as int);
                Self::lemma_seq_max_step(a@, idx as int);
            }
            if cur < mn {
                mn = cur;
            }
            if cur > mx {
                mx = cur;
            }
            idx += 1;
        }
        proof {
            assert(a@.subrange(0, n as int) =~= a@);
        }
        let steps = Self::steps_from_diff(mx - mn);
        let ghost mn0: int = mn as int;
        let ghost mx0: int = mx as int;
        proof {
            assert(mn0 == Self::spec_seq_min(a@) as int);
            assert(mx0 == Self::spec_seq_max(a@) as int);
        }
        let mut ops: Vec<i64> = Vec::new();
        let mut t: i64 = 0;
        while t < steps
            invariant
                0 <= t <= steps,
                0 <= mn0 <= mx0,
                mx0 <= 1_000_000_000,
                (mn as int, mx as int) == Self::step_state(mn0, mx0, t as nat),
                Self::ops_seq(mn0, mx0, t as nat) =~= Seq::new(ops@.len(), |k: int| ops@[k] as int),
                ops@.len() == t,
            decreases steps - t,
        {
            proof {
                Self::lemma_step_state_nonneg(mn0, mx0, t as nat);
            }
            let x = if mn % 2 == 1 && mx % 2 == 0 { 1 } else { 0 };
            let ghost prev_mn = mn as int;
            let ghost prev_mx = mx as int;
            let ghost prev_ops_seq = ops@;
            ops.push(x);
            mn = (mn + x) / 2;
            mx = (mx + x) / 2;
            proof {
                let tm1: nat = t as nat;
                assert(Self::step_state(mn0, mx0, (tm1 + 1) as nat) == {
                    let prev = Self::step_state(mn0, mx0, tm1);
                    let xx = Self::opt_x(prev.0, prev.1);
                    (Self::apply_x(prev.0, xx), Self::apply_x(prev.1, xx))
                });
                assert(Self::ops_seq(mn0, mx0, (tm1 + 1) as nat) == {
                    let prev = Self::step_state(mn0, mx0, tm1);
                    let xx = Self::opt_x(prev.0, prev.1);
                    Self::ops_seq(mn0, mx0, tm1).push(xx)
                });
                assert(Seq::new(ops@.len(), |k: int| ops@[k] as int)
                    =~= Seq::new(prev_ops_seq.len(), |k: int| prev_ops_seq[k] as int).push(x as int));
            }
            t += 1;
        }
        proof {
            Self::lemma_convergence(mn0, mx0);
            let steps_int = halving_steps(mx0 - mn0);
            assert(steps as int == steps_int);
            assert(t as nat == steps_int as nat);
            let fin = Self::step_state(mn0, mx0, steps_int as nat);
            assert(fin.0 == fin.1);
            assert((mn as int, mx as int) == fin);
            let ops_int = Self::ops_seq(mn0, mx0, t as nat);
            let ops64 = Seq::new(ops@.len(), |k: int| ops@[k] as i64);
            assert(ops@ =~= ops64);
            Self::lemma_ops_seq_bound(mn0, mx0, t as nat);
            assert(ops_int =~= Seq::new(ops@.len(), |k: int| ops@[k] as int));
            assert forall|k: int| 0 <= k < ops@.len() implies
                0 <= #[trigger] ops@[k] <= 1_000_000_000_000_000_000 by {
                assert(ops@[k] as int == ops_int[k]);
            }
            Self::lemma_apply_x_seq_len(a@, ops64);
            assert forall|i: int| 0 <= i < a.len() implies #[trigger] Self::apply_x_seq(a@, ops64)[i] == mn as i64 by {
                Self::lemma_seq_min_max_bound(a@);
                assert(mn0 <= a@[i] as int <= mx0);
                Self::lemma_sandwich(mn0, mx0, a@[i] as int, t as nat);
                assert(Self::apply_x_scalar_seq(a@[i] as int, ops_int) as int == mn as int);
                Self::lemma_apply_x_seq_pointwise(a@, ops_int, i);
                assert(Seq::new(ops_int.len(), |k: int| ops_int[k] as i64) =~= ops64);
            }
            assert(Self::all_equal(Self::apply_x_seq(a@, ops@)));
        }
        ops
    }
}

}
