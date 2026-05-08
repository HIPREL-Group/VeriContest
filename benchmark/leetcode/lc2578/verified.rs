use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    // === Spec functions ===

    pub open spec fn digit_count(n: int, d: int) -> int
        decreases n,
    {
        if n <= 0 { 0 }
        else { (if n % 10 == d { 1int } else { 0int }) + Self::digit_count(n / 10, d) }
    }

    pub open spec fn total_digits(n: int) -> int
        decreases n,
    {
        if n <= 0 { 0 }
        else { 1 + Self::total_digits(n / 10) }
    }

    pub open spec fn pow10(n: int) -> int
        decreases n,
    {
        if n <= 0 { 1 }
        else { 10 * Self::pow10(n - 1) }
    }

    pub open spec fn cnt_sum(s: Seq<i32>) -> int {
        s[0] as int + s[1] as int + s[2] as int + s[3] as int + s[4] as int
        + s[5] as int + s[6] as int + s[7] as int + s[8] as int + s[9] as int
    }

    pub open spec fn valid_split_sum(num: int, a: int, b: int) -> bool {
        a >= 0 && b >= 0
        && forall|d: int| 1 <= d <= 9 ==>
            #[trigger] Self::digit_count(num, d) == Self::digit_count(a, d) + Self::digit_count(b, d)
    }

    pub open spec fn digit_count_seq(n: int) -> Seq<int> {
        seq![
            Self::digit_count(n, 0), Self::digit_count(n, 1), Self::digit_count(n, 2),
            Self::digit_count(n, 3), Self::digit_count(n, 4), Self::digit_count(n, 5),
            Self::digit_count(n, 6), Self::digit_count(n, 7), Self::digit_count(n, 8),
            Self::digit_count(n, 9)
        ]
    }

    pub open spec fn i32_seq_to_int(s: Seq<i32>) -> Seq<int> {
        seq![s[0] as int, s[1] as int, s[2] as int, s[3] as int, s[4] as int,
             s[5] as int, s[6] as int, s[7] as int, s[8] as int, s[9] as int]
    }

    pub open spec fn greedy_sum(cnt: Seq<int>, d: int, a: int, b: int, turn_a: bool) -> int
        decreases 10 - d, if 0 <= d <= 9 && cnt.len() == 10 { cnt[d] } else { 0int },
    {
        if d < 0 || d > 9 || cnt.len() != 10 { a + b }
        else if cnt[d] <= 0 { Self::greedy_sum(cnt, d + 1, a, b, turn_a) }
        else if turn_a {
            Self::greedy_sum(cnt.update(d, cnt[d] - 1), d, a * 10 + d, b, false)
        } else {
            Self::greedy_sum(cnt.update(d, cnt[d] - 1), d, a, b * 10 + d, true)
        }
    }

    pub open spec fn min_split_sum(num: int) -> int {
        Self::greedy_sum(Self::digit_count_seq(num), 0, 0, 0, true)
    }

    // === Proof lemmas ===

    proof fn lemma_digit_count_nonneg(n: int, d: int)
        ensures Self::digit_count(n, d) >= 0,
        decreases n,
    {
        if n > 0 {
            Self::lemma_digit_count_nonneg(n / 10, d);
        }
    }

    proof fn lemma_digit_count_le_total(n: int, d: int)
        ensures Self::digit_count(n, d) <= Self::total_digits(n),
        decreases n,
    {
        if n > 0 {
            Self::lemma_digit_count_le_total(n / 10, d);
        }
    }

    proof fn lemma_total_digits_lt_pow10(n: int, k: nat)
        requires 0 <= n, n < Self::pow10(k as int),
        ensures Self::total_digits(n) <= k as int,
        decreases k,
    {
        if n > 0 {
            assert(k > 0) by {
                assert(Self::pow10(0) == 1) by(compute);
            };
            Self::lemma_total_digits_lt_pow10(n / 10, (k - 1) as nat);
        }
    }

    proof fn lemma_total_digits_bound(n: int)
        requires 0 <= n <= 1_000_000_000,
        ensures Self::total_digits(n) <= 10,
    {
        assert(Self::pow10(10) == 10000000000int) by(compute);
        Self::lemma_total_digits_lt_pow10(n, 10);
    }

    proof fn lemma_digit_count_append(n: int, d: int, e: int)
        requires
            n >= 0,
            0 <= d <= 9,
            1 <= e <= 9,
        ensures
            Self::digit_count(n * 10 + d, e) == Self::digit_count(n, e) + (if d == e { 1int } else { 0int }),
    {
        assert((n * 10 + d) % 10 == d) by(nonlinear_arith)
            requires 0 <= d <= 9, n >= 0;
        assert((n * 10 + d) / 10 == n) by(nonlinear_arith)
            requires 0 <= d <= 9, n >= 0;
        if n == 0 && d == 0 {
        } else {
            assert(n * 10 + d > 0) by(nonlinear_arith)
                requires n >= 0, d >= 0, (n > 0 || d > 0);
        }
    }

    proof fn lemma_pow10_pos(n: int)
        ensures Self::pow10(n) >= 1,
        decreases n,
    {
        if n > 0 {
            Self::lemma_pow10_pos(n - 1);
        }
    }

    proof fn lemma_pow10_mul_add(a: int, d: int, k: int)
        requires
            0 <= a,
            a < Self::pow10(k),
            0 <= d <= 9,
            k >= 0,
        ensures
            a * 10 + d < Self::pow10(k + 1),
    {
        Self::lemma_pow10_pos(k);
    }

    proof fn lemma_pow10_mono(a: int, b: int)
        requires a <= b,
        ensures Self::pow10(a) <= Self::pow10(b),
        decreases b - a,
    {
        if a < b {
            Self::lemma_pow10_mono(a, b - 1);
            Self::lemma_pow10_pos(b - 1);
        }
    }

    proof fn lemma_total_eq_cnt_sum_of_digit_counts(n: int)
        ensures
            Self::total_digits(n) ==
                Self::digit_count(n, 0) + Self::digit_count(n, 1) + Self::digit_count(n, 2)
                + Self::digit_count(n, 3) + Self::digit_count(n, 4) + Self::digit_count(n, 5)
                + Self::digit_count(n, 6) + Self::digit_count(n, 7) + Self::digit_count(n, 8)
                + Self::digit_count(n, 9),
        decreases n,
    {
        if n > 0 {
            Self::lemma_total_eq_cnt_sum_of_digit_counts(n / 10);
        }
    }

    proof fn lemma_cnt_sum_update(s: Seq<i32>, idx: int, new_val: i32)
        requires
            s.len() >= 10,
            0 <= idx < 10,
        ensures
            Self::cnt_sum(s.update(idx, new_val)) == Self::cnt_sum(s) - s[idx] as int + new_val as int,
    {
        let t = s.update(idx, new_val);
        assert(t[0] == if idx == 0 { new_val } else { s[0] });
        assert(t[1] == if idx == 1 { new_val } else { s[1] });
        assert(t[2] == if idx == 2 { new_val } else { s[2] });
        assert(t[3] == if idx == 3 { new_val } else { s[3] });
        assert(t[4] == if idx == 4 { new_val } else { s[4] });
        assert(t[5] == if idx == 5 { new_val } else { s[5] });
        assert(t[6] == if idx == 6 { new_val } else { s[6] });
        assert(t[7] == if idx == 7 { new_val } else { s[7] });
        assert(t[8] == if idx == 8 { new_val } else { s[8] });
        assert(t[9] == if idx == 9 { new_val } else { s[9] });
    }

    proof fn lemma_cnt_sum_nonneg_implies_zero(s: Seq<i32>)
        requires
            s.len() >= 10,
            forall|e: int| 0 <= e <= 9 ==> #[trigger] s[e] >= 0,
            Self::cnt_sum(s) == 0,
        ensures
            forall|e: int| 0 <= e <= 9 ==> s[e] == 0,
    {
    }

    proof fn lemma_i32_seq_to_int_update(s: Seq<i32>, idx: int, val: i32)
        requires s.len() >= 10, 0 <= idx <= 9,
        ensures Self::i32_seq_to_int(s.update(idx, val)) =~= Self::i32_seq_to_int(s).update(idx, val as int),
    {
        let t = s.update(idx, val);
        assert(t[0] == if idx == 0 { val } else { s[0] });
        assert(t[1] == if idx == 1 { val } else { s[1] });
        assert(t[2] == if idx == 2 { val } else { s[2] });
        assert(t[3] == if idx == 3 { val } else { s[3] });
        assert(t[4] == if idx == 4 { val } else { s[4] });
        assert(t[5] == if idx == 5 { val } else { s[5] });
        assert(t[6] == if idx == 6 { val } else { s[6] });
        assert(t[7] == if idx == 7 { val } else { s[7] });
        assert(t[8] == if idx == 8 { val } else { s[8] });
        assert(t[9] == if idx == 9 { val } else { s[9] });
    }

    // === Main function ===

    pub fn split_num(num: i32) -> (result: i32)
        requires
            10 <= num <= 1_000_000_000,
        ensures
            result >= 0,
            exists|a: int, b: int|
                #[trigger] Self::valid_split_sum(num as int, a, b)
                && result as int == a + b,
            result as int == Self::min_split_sum(num as int),
    {
        let ghost old_num = num as int;

        proof {
            Self::lemma_total_digits_bound(old_num);
        }

        // Phase 1: Count digit frequencies
        let mut cnt: Vec<i32> = vec![0; 10];
        let mut x = num;

        while x > 0
            invariant
                0 <= x,
                cnt.len() == 10,
                forall|e: int| 0 <= e <= 9 ==> #[trigger] cnt[e] >= 0,
                forall|e: int| 0 <= e <= 9 ==>
                    cnt[e] as int + Self::digit_count(x as int, e) == Self::digit_count(old_num, e),
                forall|e: int| 0 <= e <= 9 ==> cnt[e] <= 10,
                Self::total_digits(old_num) <= 10,
            decreases x,
        {
            let d = (x % 10) as usize;
            proof {
                Self::lemma_digit_count_nonneg(x as int / 10, d as int);
                Self::lemma_digit_count_le_total(old_num, d as int);
            }
            cnt.set(d, cnt[d] + 1);
            x = x / 10;
        }

        // After Phase 1: cnt matches digit_count_seq
        proof {
            Self::lemma_total_eq_cnt_sum_of_digit_counts(old_num);
            assert(Self::i32_seq_to_int(cnt@) =~= Self::digit_count_seq(old_num));
        }

        let ghost target = Self::min_split_sum(old_num);

        // Phase 2: Distribute digits alternately to a and b
        let mut a: i32 = 0;
        let mut b: i32 = 0;
        let mut turn_a = true;
        let mut d: usize = 0;

        let ghost mut na: int = 0;
        let ghost mut nb: int = 0;

        while d <= 9
            invariant
                0 <= d <= 10,
                cnt.len() == 10,
                a >= 0,
                b >= 0,
                na >= 0,
                nb >= 0,
                a < Self::pow10(na),
                b < Self::pow10(nb),
                turn_a ==> na == nb,
                !turn_a ==> na == nb + 1,
                na + nb + Self::cnt_sum(cnt@) == Self::total_digits(old_num),
                Self::total_digits(old_num) <= 10,
                forall|e: int| 0 <= e <= 9 ==> #[trigger] cnt[e] >= 0,
                forall|e: int| 1 <= e <= 9 ==>
                    Self::digit_count(a as int, e) + Self::digit_count(b as int, e)
                    + cnt[e] as int == Self::digit_count(old_num, e),
                forall|e: int| 0 <= e < d as int ==> cnt[e] == 0,
                Self::greedy_sum(Self::i32_seq_to_int(cnt@), d as int, a as int, b as int, turn_a) == target,
            decreases 10 - d,
        {
            while cnt[d] > 0
                invariant
                    cnt.len() == 10,
                    0 <= d <= 9,
                    a >= 0,
                    b >= 0,
                    na >= 0,
                    nb >= 0,
                    a < Self::pow10(na),
                    b < Self::pow10(nb),
                    turn_a ==> na == nb,
                    !turn_a ==> na == nb + 1,
                    na + nb + Self::cnt_sum(cnt@) == Self::total_digits(old_num),
                    Self::total_digits(old_num) <= 10,
                    forall|e: int| 0 <= e <= 9 ==> #[trigger] cnt[e] >= 0,
                    forall|e: int| 1 <= e <= 9 ==>
                        Self::digit_count(a as int, e) + Self::digit_count(b as int, e)
                        + cnt[e] as int == Self::digit_count(old_num, e),
                    forall|e: int| 0 <= e < d as int ==> cnt[e] == 0,
                    Self::greedy_sum(Self::i32_seq_to_int(cnt@), d as int, a as int, b as int, turn_a) == target,
                decreases cnt[d as int] as int,
            {
                let ghost old_a = a as int;
                let ghost old_b = b as int;
                let ghost old_cnt_seq = cnt@;
                let ghost old_turn = turn_a;
                let ghost old_cnt_int = Self::i32_seq_to_int(old_cnt_seq);

                proof {
                    assert(Self::cnt_sum(cnt@) >= 1) by {
                        assert(cnt@[d as int] >= 1);
                        assert(cnt@[0] >= 0);
                        assert(cnt@[1] >= 0);
                        assert(cnt@[2] >= 0);
                        assert(cnt@[3] >= 0);
                        assert(cnt@[4] >= 0);
                        assert(cnt@[5] >= 0);
                        assert(cnt@[6] >= 0);
                        assert(cnt@[7] >= 0);
                        assert(cnt@[8] >= 0);
                        assert(cnt@[9] >= 0);
                    };
                    assert(na + nb <= 9);
                    assert(old_cnt_int[d as int] > 0);
                    assert(old_cnt_int.len() == 10);
                }

                if turn_a {
                    proof {
                        assert(na <= 4);
                        Self::lemma_pow10_mono(na, 4);
                        assert(Self::pow10(4) == 10000) by(compute);
                        assert(a < 10000);
                        Self::lemma_pow10_mul_add(a as int, d as int, na);
                    }
                    a = a * 10 + d as i32;
                    proof {
                        assert forall|e: int| 1 <= e <= 9 implies
                            Self::digit_count(a as int, e) == Self::digit_count(old_a, e) + (if d as int == e { 1int } else { 0int })
                        by {
                            Self::lemma_digit_count_append(old_a, d as int, e);
                        };
                        na = na + 1;
                    }
                } else {
                    proof {
                        assert(nb <= 4);
                        Self::lemma_pow10_mono(nb, 4);
                        assert(Self::pow10(4) == 10000) by(compute);
                        assert(b < 10000);
                        Self::lemma_pow10_mul_add(b as int, d as int, nb);
                    }
                    b = b * 10 + d as i32;
                    proof {
                        assert forall|e: int| 1 <= e <= 9 implies
                            Self::digit_count(b as int, e) == Self::digit_count(old_b, e) + (if d as int == e { 1int } else { 0int })
                        by {
                            Self::lemma_digit_count_append(old_b, d as int, e);
                        };
                        nb = nb + 1;
                    }
                }

                turn_a = !turn_a;

                proof {
                    Self::lemma_cnt_sum_update(old_cnt_seq, d as int, (old_cnt_seq[d as int] - 1) as i32);
                }
                cnt.set(d, cnt[d] - 1);

                // Prove greedy_sum invariant is maintained
                proof {
                    Self::lemma_i32_seq_to_int_update(old_cnt_seq, d as int, (old_cnt_seq[d as int] - 1) as i32);
                    let new_cnt_int = Self::i32_seq_to_int(cnt@);
                    assert(new_cnt_int =~= old_cnt_int.update(d as int, old_cnt_int[d as int] - 1));
                }
            }

            // After inner loop: cnt[d] == 0, greedy_sum skips to d+1
            proof {
                assert(cnt@[d as int] == 0);
                let cnt_int = Self::i32_seq_to_int(cnt@);
                assert(cnt_int[d as int] == 0);
                assert(cnt_int[d as int] <= 0);
                assert(cnt_int.len() == 10);
                assert(0 <= d as int <= 9);
            }
            d = d + 1;
        }

        // Prove final bounds and existential
        proof {
            Self::lemma_pow10_mono(na, 5);
            Self::lemma_pow10_mono(nb, 5);
            assert(Self::pow10(5) == 100000) by(compute);

            // All cnt consumed
            assert(Self::cnt_sum(cnt@) == 0) by {
                Self::lemma_total_eq_cnt_sum_of_digit_counts(old_num);
                assert forall|e: int| 0 <= e <= 9 implies Self::digit_count(old_num, e) >= 0 by {
                    Self::lemma_digit_count_nonneg(old_num, e);
                };
            };

            Self::lemma_cnt_sum_nonneg_implies_zero(cnt@);

            let wa = a as int;
            let wb = b as int;
            assert forall|dd: int| 1 <= dd <= 9 implies
                Self::digit_count(old_num, dd) == Self::digit_count(wa, dd) + Self::digit_count(wb, dd)
            by {
                assert(cnt@[dd] == 0);
            };
            assert(Self::valid_split_sum(old_num, wa, wb));

            // greedy_sum with d=10 returns a+b
            let cnt_int = Self::i32_seq_to_int(cnt@);
            assert(Self::greedy_sum(cnt_int, 10, wa, wb, turn_a) == wa + wb);
            assert(wa + wb == target);
        }

        a + b
    }
}

}
