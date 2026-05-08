use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_power10(p: int) -> bool
        decreases p,
    {
        if p < 1 {
            false
        } else if p == 1 {
            true
        } else {
            p % 10 == 0 && Self::is_power10(p / 10)
        }
    }

    pub open spec fn is_base10_component(x: int) -> bool {
        exists|d: int, p: int| 1 <= d <= 9 && p >= 1 && Self::is_power10(p) && x == #[trigger] (d * p)
    }

    pub open spec fn count_nonzero_digits(n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::count_nonzero_digits(n / 10) + if n % 10 == 0 { 0int } else { 1int }
        }
    }

    pub open spec fn spec_sum_prefix(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::spec_sum_prefix(s, end - 1) + s[end - 1] as int
        }
    }

    pub proof fn lemma_power10_mul10(p: int)
        requires
            Self::is_power10(p),
        ensures
            Self::is_power10(p * 10),
    {
        assert(p >= 1);
        assert((p * 10) % 10 == 0);
        assert((p * 10) / 10 == p);
    }

    pub proof fn lemma_sum_prefix_step(s: Seq<i32>, end: int)
        requires
            0 < end <= s.len(),
        ensures
            Self::spec_sum_prefix(s, end) == Self::spec_sum_prefix(s, end - 1) + s[end - 1] as int,
    {
    }

    pub proof fn lemma_sum_prefix_push_prefix(s: Seq<i32>, x: i32, end: int)
        requires
            0 <= end <= s.len(),
        ensures
            Self::spec_sum_prefix(s.push(x), end) == Self::spec_sum_prefix(s, end),
        decreases end,
    {
        if end > 0 {
            Self::lemma_sum_prefix_push_prefix(s, x, end - 1);
        }
    }

    pub proof fn lemma_sum_prefix_push_last(s: Seq<i32>, x: i32)
        ensures
            Self::spec_sum_prefix(s.push(x), s.len() + 1int) == Self::spec_sum_prefix(s, s.len() as int)
                + x as int,
    {
        Self::lemma_sum_prefix_step(s.push(x), s.len() + 1int);
        Self::lemma_sum_prefix_push_prefix(s, x, s.len() as int);
    }

    pub fn decimal_representation(n: i32) -> (result: Vec<i32>)
        requires
            1 <= n <= 1_000_000_000,
        ensures
            result.len() == Self::count_nonzero_digits(n as int),
            Self::spec_sum_prefix(result@, result.len() as int) == n,
            forall|i: int| 0 <= i < result.len() ==> Self::is_base10_component(#[trigger] result[i] as int),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] > #[trigger] result[j],
    {
        let mut m: i64 = n as i64;
        let mut place: i64 = 1;
        let mut asc: Vec<i32> = Vec::new();
        while m > 0
            invariant
                1 <= n <= 1_000_000_000,
                0 <= m,
                1 <= place <= 10_000_000_000,
                Self::is_power10(place as int),
                0 <= Self::spec_sum_prefix(asc@, asc.len() as int),
                Self::spec_sum_prefix(asc@, asc.len() as int) + m as int * place as int == n as int,
                asc.len() + Self::count_nonzero_digits(m as int) == Self::count_nonzero_digits(n as int),
                forall|i: int| 0 <= i < asc.len() ==> Self::is_base10_component(#[trigger] asc[i] as int),
                forall|i: int| 0 <= i < asc.len() ==> 0 < #[trigger] asc[i] < place as int,
                forall|i: int, j: int| 0 <= i < j < asc.len() ==> #[trigger] asc[i] < #[trigger] asc[j],
            decreases m,
        {
            let ghost old_seq = asc@;
            let ghost old_m: int = m as int;
            let ghost old_place: int = place as int;
            let ghost old_sum = Self::spec_sum_prefix(old_seq, old_seq.len() as int);

            let digit: i64 = m % 10;
            if digit != 0 {
                proof {
                    assert(1 <= digit <= 9);
                    assert(old_m == 10 * (old_m / 10) + old_m % 10);
                    assert(digit as int == old_m % 10);
                    assert(0 <= old_m / 10);
                    assert(old_m >= digit as int) by (nonlinear_arith)
                        requires
                            old_m == 10 * (old_m / 10) + digit as int,
                            0 <= old_m / 10,
                    ;
                    assert(0 <= old_sum);
                    assert(old_m * old_place <= n as int) by (nonlinear_arith)
                        requires
                            old_sum + old_m * old_place == n as int,
                            0 <= old_sum,
                    ;
                    assert(digit as int * old_place <= old_m * old_place) by (nonlinear_arith)
                        requires
                            old_m >= digit as int,
                            1 <= old_place,
                    ;
                    assert(0 < digit as int * old_place <= n as int) by (nonlinear_arith)
                        requires
                            1 <= digit as int,
                            1 <= old_place,
                            digit as int * old_place <= old_m * old_place,
                            old_m * old_place <= n as int,
                    ;
                    assert((digit * place) as int == digit as int * old_place);
                    assert(n as int <= i32::MAX);
                    assert((digit * place) as int <= i32::MAX) by (nonlinear_arith)
                        requires
                            (digit * place) as int == digit as int * old_place,
                            digit as int * old_place <= n as int,
                            n as int <= i32::MAX,
                    ;
                    assert(exists|d: int, p: int| 1 <= d <= 9 && p >= 1 && Self::is_power10(p) && (digit as int * old_place) == #[trigger] (d * p));
                }
                asc.push((digit * place) as i32);
            }

            m = m / 10;
            proof {
                assert(old_m == 10 * (m as int) + digit as int);
                if digit == 0 {
                    assert(Self::spec_sum_prefix(asc@, asc.len() as int) == old_sum + digit as int * old_place);
                } else {
                    let x = (digit * place) as i32;
                    assert(old_seq.push(x) == asc@);
                    Self::lemma_sum_prefix_push_last(old_seq, x);
                    assert((digit * place) as int == digit as int * old_place);
                    assert(Self::spec_sum_prefix(asc@, asc.len() as int) == Self::spec_sum_prefix(old_seq.push(x), old_seq.len() + 1int));
                    assert(Self::spec_sum_prefix(asc@, asc.len() as int) == old_sum + digit as int * old_place);
                }
                assert(Self::count_nonzero_digits(old_m) == Self::count_nonzero_digits(m as int) + if digit == 0 { 0int } else { 1int });
                if digit == 0 {
                    assert(asc.len() == old_seq.len());
                } else {
                    assert(asc.len() == old_seq.len() + 1);
                }
                assert(old_m >= 1);
                assert(old_place <= 1_000_000_000) by (nonlinear_arith)
                    requires
                        old_sum + old_m * old_place == n as int,
                        0 <= old_sum,
                        old_m >= 1,
                        n as int <= 1_000_000_000,
                ;
                assert(Self::spec_sum_prefix(asc@, asc.len() as int) + m as int * (old_place * 10) == n as int) by (nonlinear_arith)
                    requires
                        old_m == 10 * (m as int) + digit as int,
                        Self::spec_sum_prefix(asc@, asc.len() as int) == old_sum + digit as int * old_place,
                        old_sum + old_m * old_place == n as int,
                ;
                assert forall|i: int| 0 <= i < asc.len() implies 0 < #[trigger] asc[i] && asc[i] < old_place * 10 by {
                    if digit != 0 && i == old_seq.len() {
                        let x = (digit * place) as i32;
                        assert(asc@[i] == x);
                        assert((digit * place) as int == (digit as int) * old_place);
                        assert(0 < (digit as int) * old_place) by (nonlinear_arith)
                            requires
                                1 <= digit as int,
                                1 <= old_place,
                        ;
                        assert((digit as int) * old_place < old_place * 10) by (nonlinear_arith)
                            requires
                                digit as int <= 9,
                                1 <= old_place,
                        ;
                    } else {
                        assert(0 < (asc@[i] as int));
                        assert((asc@[i] as int) < old_place);
                        assert(old_place < old_place * 10);
                    }
                }
                assert forall|i: int, j: int| 0 <= i < j < asc.len() implies #[trigger] asc[i] < #[trigger] asc[j] by {
                    if digit != 0 && j == old_seq.len() {
                        assert((asc@[i] as int) < old_place);
                        assert((digit as int) * old_place >= old_place) by (nonlinear_arith)
                            requires
                                1 <= digit as int,
                                1 <= old_place,
                        ;
                        assert((digit * place) as int == (digit as int) * old_place);
                        assert(asc@[j] == (digit * place) as i32);
                    } else {
                        assert(old_seq[i] < old_seq[j]);
                    }
                }
                assert(old_place * 10 <= 10_000_000_000) by (nonlinear_arith)
                    requires
                        old_place <= 1_000_000_000,
                ;
            }
            proof {
                Self::lemma_power10_mul10(place as int);
            }
            place = place * 10;
        }

        let mut result: Vec<i32> = Vec::with_capacity(asc.len());
        let mut i: usize = asc.len();
        while i > 0
            invariant
                0 <= i <= asc.len(),
                result.len() + i == asc.len(),
                forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j] == asc[asc.len() - 1 - j],
                Self::spec_sum_prefix(result@, result.len() as int) + Self::spec_sum_prefix(asc@, i as int) == n,
            decreases i,
        {
            let ghost old_i: int = i as int;
            let ghost old_result = result@;
            i = i - 1;
            let x = asc[i];
            proof {
                Self::lemma_sum_prefix_step(asc@, old_i);
                assert(old_i == i as int + 1);
                assert(Self::spec_sum_prefix(asc@, old_i) == Self::spec_sum_prefix(asc@, i as int) + x as int);
            }
            result.push(x);
            proof {
                assert(result@ == old_result.push(x));
                Self::lemma_sum_prefix_push_last(old_result, x);
                assert(Self::spec_sum_prefix(result@, result.len() as int) == Self::spec_sum_prefix(old_result, old_result.len() as int) + x as int);
                assert(Self::spec_sum_prefix(old_result, old_result.len() as int) + Self::spec_sum_prefix(asc@, old_i) == n);
                assert(Self::spec_sum_prefix(result@, result.len() as int) + Self::spec_sum_prefix(asc@, i as int) == n);
            }
        }

        proof {
            assert(i == 0);
            assert(result.len() == asc.len());
            assert(Self::count_nonzero_digits(0) == 0);
            assert(result.len() == Self::count_nonzero_digits(n as int));
            assert(Self::spec_sum_prefix(asc@, 0) == 0);
            assert(Self::spec_sum_prefix(result@, result.len() as int) == n);

            assert forall|k: int| 0 <= k < result.len() implies Self::is_base10_component(#[trigger] result[k] as int) by {
                assert(result[k] == asc[asc.len() - 1 - k]);
                assert(0 <= asc.len() - 1 - k < asc.len());
                assert(Self::is_base10_component(asc[asc.len() - 1 - k] as int));
            }

            assert forall|a: int, b: int| 0 <= a < b < result.len() implies #[trigger] result[a] > #[trigger] result[b] by {
                let ia = asc.len() - 1 - a;
                let ib = asc.len() - 1 - b;
                assert(0 <= ib < ia < asc.len());
                assert(asc[ib] < asc[ia]);
                assert(result[a] == asc[ia]);
                assert(result[b] == asc[ib]);
            }
        }

        result
    }
}

}
