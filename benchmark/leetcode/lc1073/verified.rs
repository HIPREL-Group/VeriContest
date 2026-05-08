use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn negabinary_val(s: Seq<i32>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0int
    } else {
        s.last() as int + (-2int) * negabinary_val(s.drop_last())
    }
}

pub open spec fn val_lsb(s: Seq<i32>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0int
    } else {
        s[0] as int + (-2int) * val_lsb(s.subrange(1, s.len() as int))
    }
}

pub open spec fn pow_neg2(n: nat) -> int
    decreases n,
{
    if n == 0 {
        1int
    } else {
        (-2int) * pow_neg2((n - 1) as nat)
    }
}

pub open spec fn suffix_val(s: Seq<i32>, k: nat) -> int {
    negabinary_val(
        s.subrange(
            if k as int >= s.len() { 0int } else { s.len() as int - k as int },
            s.len() as int,
        ),
    )
}

pub open spec fn get_digit(s: Seq<i32>, k: nat) -> int {
    if (k as int) < s.len() {
        s[s.len() - 1 - k as int] as int
    } else {
        0int
    }
}

proof fn lemma_prepend_val(x: i32, s: Seq<i32>)
    ensures
        negabinary_val(seq![x] + s) == x as int * pow_neg2(s.len()) + negabinary_val(s),
    decreases s.len(),
{
    let xs = seq![x] + s;
    if s.len() == 0 {
        assert(xs =~= seq![x]);
        assert(xs.drop_last() =~= Seq::<i32>::empty());
        assert(xs.last() == x);
        assert(negabinary_val(Seq::<i32>::empty()) == 0int);
        assert(negabinary_val(s) == 0int);
        assert(pow_neg2(s.len()) == 1int);
    } else {
        lemma_prepend_val(x, s.drop_last());
        assert(xs.last() == s.last());
        assert(xs.drop_last() =~= seq![x] + s.drop_last());
        let p = pow_neg2(s.len());
        let p_prev = pow_neg2((s.len() - 1) as nat);
        assert(p == (-2int) * p_prev);
        let inner = negabinary_val(s.drop_last());
        assert(negabinary_val(seq![x] + s.drop_last()) == x as int * p_prev + inner);
        assert((-2int) * (x as int * p_prev + inner) == x as int * p + (-2int) * inner) by (
            nonlinear_arith
        )
            requires
                p == (-2int) * p_prev,
        ;
    }
}

proof fn lemma_negabinary_val_head(s: Seq<i32>)
    requires
        s.len() > 0,
    ensures
        negabinary_val(s) == s[0] as int * pow_neg2((s.len() - 1) as nat) + negabinary_val(
            s.subrange(1, s.len() as int),
        ),
{
    let tail = s.subrange(1, s.len() as int);
    assert(seq![s[0]] + tail =~= s);
    lemma_prepend_val(s[0], tail);
}

proof fn lemma_suffix_val_step(s: Seq<i32>, k: nat)
    ensures
        suffix_val(s, (k + 1) as nat) == get_digit(s, k) * pow_neg2(k) + suffix_val(s, k),
{
    if (k as int) < s.len() {
        let suffix_new = s.subrange(s.len() as int - (k as int) - 1, s.len() as int);
        let suffix_old = s.subrange(s.len() as int - k as int, s.len() as int);
        assert(suffix_new.subrange(1, suffix_new.len() as int) =~= suffix_old);
        lemma_negabinary_val_head(suffix_new);
    }
}

proof fn lemma_suffix_val_full(s: Seq<i32>, k: nat)
    requires
        k as int >= s.len(),
    ensures
        suffix_val(s, k) == negabinary_val(s),
{
    assert(s.subrange(0int, s.len() as int) =~= s);
}

proof fn lemma_val_lsb_push(s: Seq<i32>, d: i32)
    ensures
        val_lsb(s.push(d)) == val_lsb(s) + d as int * pow_neg2(s.len()),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.push(d) =~= seq![d]);
        assert(seq![d].subrange(1, 1int) =~= Seq::<i32>::empty());
        assert(val_lsb(Seq::<i32>::empty()) == 0int);
        assert(val_lsb(s) == 0int);
        assert(pow_neg2(s.len()) == 1int);
    } else {
        let tail = s.subrange(1, s.len() as int);
        let pk = pow_neg2(s.len());
        let pk_tail = pow_neg2(tail.len());
        lemma_val_lsb_push(tail, d);
        assert(s.push(d).subrange(1, s.push(d).len() as int) =~= tail.push(d));
        assert(pk == (-2int) * pk_tail);
        let vt = val_lsb(tail);
        let dpt = d as int * pk_tail;
        assert(val_lsb(tail.push(d)) == vt + dpt);
        assert((-2int) * (vt + dpt) == (-2int) * vt + (-2int) * dpt) by (nonlinear_arith);
        assert((-2int) * dpt == d as int * pk) by (nonlinear_arith)
            requires
                pk == (-2int) * pk_tail,
                dpt == d as int * pk_tail,
        ;
        assert(val_lsb(s) == s[0] as int + (-2int) * vt);
        assert(val_lsb(s.push(d)) == s[0] as int + (-2int) * (vt + dpt));
    }
}

proof fn lemma_reverse_val(s: Seq<i32>)
    ensures
        negabinary_val(s.reverse()) == val_lsb(s),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.reverse() =~= s);
    } else {
        let tail = s.subrange(1, s.len() as int);
        lemma_reverse_val(tail);
        assert(s.reverse().drop_last() =~= tail.reverse());
        assert(s.reverse().last() == s[0]);
    }
}

proof fn lemma_val_lsb_strip_trailing_zero(s: Seq<i32>)
    requires
        s.len() > 0,
        s.last() == 0,
    ensures
        val_lsb(s) == val_lsb(s.drop_last()),
    decreases s.len(),
{
    if s.len() == 1 {
        assert(s.subrange(1, 1int) =~= Seq::<i32>::empty());
        assert(s[0] == s.last());
        assert(s[0] == 0int);
        assert(s.drop_last() =~= Seq::<i32>::empty());
    } else {
        let tail = s.subrange(1, s.len() as int);
        let dl = s.drop_last();
        assert(tail.last() == s.last());
        lemma_val_lsb_strip_trailing_zero(tail);
        assert(dl.subrange(1, dl.len() as int) =~= tail.drop_last());
        assert(dl[0] == s[0]);
        assert(val_lsb(s) == s[0] as int + (-2int) * val_lsb(tail));
        assert(val_lsb(dl) == dl[0] as int + (-2int) * val_lsb(dl.subrange(1, dl.len() as int)));
        assert(val_lsb(dl.subrange(1, dl.len() as int)) == val_lsb(tail.drop_last()));
        assert(val_lsb(tail) == val_lsb(tail.drop_last()));
        assert(val_lsb(s) == s[0] as int + (-2int) * val_lsb(tail.drop_last()));
        assert(val_lsb(dl) == s[0] as int + (-2int) * val_lsb(tail.drop_last()));
        assert(val_lsb(s) == val_lsb(s.drop_last()));
    }
}

proof fn lemma_val_lsb_strip_zeros(s: Seq<i32>, end: int)
    requires
        1 <= end <= s.len(),
        forall|i: int| end <= i < s.len() ==> s[i] == 0,
    ensures
        val_lsb(s.subrange(0, end)) == val_lsb(s),
    decreases s.len() - end,
{
    if end == s.len() {
        assert(s.subrange(0, end) =~= s);
    } else {
        assert(s.last() == 0);
        lemma_val_lsb_strip_trailing_zero(s);
        lemma_val_lsb_strip_zeros(s.drop_last(), end);
        assert(s.drop_last().subrange(0, end) =~= s.subrange(0, end));
    }
}

impl Solution {
    pub fn add_negabinary(arr1: Vec<i32>, arr2: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= arr1.len() <= 1000,
            1 <= arr2.len() <= 1000,
            forall|i: int| 0 <= i < arr1.len() ==> (#[trigger] arr1[i] == 0 || arr1[i] == 1),
            forall|i: int| 0 <= i < arr2.len() ==> (#[trigger] arr2[i] == 0 || arr2[i] == 1),
            arr1.len() == 1 || arr1[0] == 1,
            arr2.len() == 1 || arr2[0] == 1,
        ensures
            result.len() >= 1,
            forall|i: int|
                0 <= i < result.len() ==> (#[trigger] result[i] == 0 || result[i] == 1),
            result.len() == 1 || result[0] == 1,
            negabinary_val(result@) == negabinary_val(arr1@) + negabinary_val(arr2@),
    {
        let n1 = arr1.len();
        let n2 = arr2.len();
        let max_len = if n1 >= n2 { n1 } else { n2 };
        let max_iters = max_len + 3;
        let mut res: Vec<i32> = Vec::new();
        let mut carry: i32 = 0;
        let mut k: usize = 0;

        while k < max_iters && (k < n1 || k < n2 || carry != 0)
            invariant
                n1 == arr1.len(),
                n2 == arr2.len(),
                1 <= n1 <= 1000,
                1 <= n2 <= 1000,
                max_len == (if n1 >= n2 { n1 } else { n2 }),
                max_iters == max_len + 3,
                k <= max_iters,
                k == res.len(),
                -1 <= carry <= 1,
                forall|i: int|
                    0 <= i < arr1.len() ==> (#[trigger] arr1[i] == 0 || arr1[i] == 1),
                forall|i: int|
                    0 <= i < arr2.len() ==> (#[trigger] arr2[i] == 0 || arr2[i] == 1),
                forall|i: int| 0 <= i < res.len() ==> (#[trigger] res[i] == 0 || res[i] == 1),
                val_lsb(res@) + carry as int * pow_neg2(k as nat)
                    == suffix_val(arr1@, k as nat) + suffix_val(arr2@, k as nat),
                k as int > max_len as int ==> carry >= 0,
                k as int > max_len as int + 1 ==> carry == 0,
            decreases max_iters - k,
        {
            let a = if k < n1 { arr1[n1 - 1 - k] } else { 0 };
            let b = if k < n2 { arr2[n2 - 1 - k] } else { 0 };
            let sum = carry + a + b;

            let bit: i32;
            let new_carry: i32;
            if sum >= 2 {
                bit = sum - 2;
                new_carry = -1;
            } else if sum < 0 {
                bit = sum + 2;
                new_carry = 1;
            } else {
                bit = sum;
                new_carry = 0;
            }

            proof {
                let pk = pow_neg2(k as nat);
                assert(pow_neg2((k + 1) as nat) == (-2int) * pk);
                assert(sum as int == bit as int + (-2int) * new_carry as int);

                lemma_val_lsb_push(res@, bit);
                lemma_suffix_val_step(arr1@, k as nat);
                lemma_suffix_val_step(arr2@, k as nat);
                assert(get_digit(arr1@, k as nat) == a as int);
                assert(get_digit(arr2@, k as nat) == b as int);

                assert(new_carry as int * ((-2int) * pk) == (-2int) * new_carry as int * pk) by (
                    nonlinear_arith
                );
                assert((bit as int + (-2int) * new_carry as int) * pk == bit as int * pk + (-2int)
                    * new_carry as int * pk) by (nonlinear_arith);
                assert((carry as int + a as int + b as int) * pk == carry as int * pk + (a as int
                    + b as int) * pk) by (nonlinear_arith);
                assert((a as int + b as int) * pk == a as int * pk + b as int * pk) by (
                    nonlinear_arith
                );
            }

            res.push(bit);
            carry = new_carry;
            k = k + 1;
        }

        proof {
            if carry != 0 {
                assert(k as int > max_len as int + 1);
                assert(carry == 0);
            }
            lemma_suffix_val_full(arr1@, k as nat);
            lemma_suffix_val_full(arr2@, k as nat);
        }

        let mut end = res.len();
        while end > 1 && res[end - 1] == 0
            invariant
                1 <= end <= res.len(),
                forall|i: int| 0 <= i < res.len() ==> (#[trigger] res[i] == 0 || res[i] == 1),
                forall|i: int| end as int <= i < res.len() ==> res[i] == 0,
                val_lsb(res@) == negabinary_val(arr1@) + negabinary_val(arr2@),
            decreases end,
        {
            end = end - 1;
        }

        proof {
            lemma_val_lsb_strip_zeros(res@, end as int);
        }

        let mut result: Vec<i32> = Vec::new();
        let mut i = end;
        while i > 0
            invariant
                0 <= i <= end,
                1 <= end <= res.len(),
                result.len() == end - i,
                forall|j: int|
                    0 <= j < result.len() ==> #[trigger] result[j] == res[(end - 1 - j) as int],
                forall|j: int| 0 <= j < res.len() ==> (res[j] == 0 || res[j] == 1),
                end > 1 ==> res[end - 1] != 0,
            decreases i,
        {
            i = i - 1;
            result.push(res[i]);
        }

        proof {
            assert(result@ =~= res@.subrange(0, end as int).reverse());
            lemma_reverse_val(res@.subrange(0, end as int));
            if result.len() > 1 {
                assert(result[0] == res[end - 1]);
            }
        }

        result
    }
}

}
