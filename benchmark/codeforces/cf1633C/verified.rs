use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use vstd::arithmetic::mul::{
    lemma_mul_is_commutative, lemma_mul_is_distributive_add, lemma_mul_inequality,
};

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_ceil_div_pos(num: int, den: int) -> int
        recommends
            num >= 1,
            den >= 1,
    {
        1 + (num - 1) / den
    }

    pub open spec fn spec_effective_hp(h_c: int, k: int, a: int, weapon_upgrades: int) -> int {
        h_c + (k - weapon_upgrades) * a
    }

    pub open spec fn spec_effective_attack(d_c: int, w: int, weapon_upgrades: int) -> int {
        d_c + weapon_upgrades * w
    }

    pub open spec fn spec_player_wins(hc: int, dc: int, hm: int, dm: int) -> bool {
        let strikes = Self::spec_ceil_div_pos(hm, dc);
        hc > (strikes - 1) * dm
    }

    pub open spec fn spec_win_exists_upto(
        h_c: int,
        d_c: int,
        h_m: int,
        d_m: int,
        k: int,
        w: int,
        a: int,
        exclusive_end: int,
    ) -> bool {
        exists|weapon_upgrades: int|
            #![auto]
            0 <= weapon_upgrades < exclusive_end && Self::spec_player_wins(
                Self::spec_effective_hp(h_c, k, a, weapon_upgrades),
                Self::spec_effective_attack(d_c, w, weapon_upgrades),
                h_m,
                d_m,
            )
    }

    pub open spec fn spec_can_slay(
        h_c: int,
        d_c: int,
        h_m: int,
        d_m: int,
        k: int,
        w: int,
        a: int,
    ) -> bool {
        Self::spec_win_exists_upto(h_c, d_c, h_m, d_m, k, w, a, k + 1)
    }

    proof fn lemma_int_win_cmp_div(hc: int, dm: int, kk: int)
        requires
            hc >= 1,
            dm >= 1,
            kk >= 0,
        ensures
            (hc > kk * dm) == (kk <= (hc - 1) / dm),
    {
        assert((hc > kk * dm) == (kk * dm < hc));
        assert((kk * dm < hc) == (kk * dm <= hc - 1));
        let x = hc - 1;
        let q = x / dm;
        lemma_fundamental_div_mod(x, dm);
        assert(x == dm * (x / dm) + (x % dm));
        assert(q == x / dm);
        assert(x == dm * q + (x % dm));
        assert(0 <= (x % dm) < dm);
        assert((kk * dm <= x) == (kk <= q)) by {
            assert((kk <= q) ==> (kk * dm <= x)) by {
                if kk <= q {
                    lemma_mul_inequality(kk, q, dm);
                    assert(kk * dm <= q * dm);
                    lemma_mul_is_commutative(q, dm);
                    assert(q * dm == dm * q);
                    assert(dm * q <= dm * q + (x % dm));
                    assert(dm * q + (x % dm) == x);
                    assert(kk * dm <= x);
                }
            };
            assert((kk * dm <= x) ==> (kk <= q)) by {
                if !(kk <= q) {
                    assert(kk >= q + 1);
                    lemma_mul_inequality(q + 1, kk, dm);
                    assert((q + 1) * dm <= kk * dm);
                    lemma_mul_is_distributive_add(dm, q, 1);
                    assert(dm * (q + 1) == dm * q + dm);
                    lemma_mul_is_commutative(q + 1, dm);
                    lemma_mul_is_commutative(q, dm);
                    assert((q + 1) * dm == q * dm + dm);
                    assert(dm * q + dm > dm * q + (x % dm)) by (nonlinear_arith)
                        requires
                            0 <= (x % dm) < dm,
                    ;
                    assert(dm * q + (x % dm) == x);
                    assert((q + 1) * dm > x);
                    assert(kk * dm >= (q + 1) * dm);
                    assert(kk * dm > x);
                    assert(!(kk * dm <= x));
                }
            };
        };
        assert(q == (hc - 1) / dm);
    }

    proof fn lemma_win_exists_upto_succ(
        h_c: int,
        d_c: int,
        h_m: int,
        d_m: int,
        k: int,
        w: int,
        a: int,
        i: int,
    )
        requires
            0 <= i <= k,
            1 <= h_c,
            1 <= d_c,
            1 <= h_m,
            1 <= d_m,
            0 <= w,
            0 <= a,
        ensures
            Self::spec_win_exists_upto(h_c, d_c, h_m, d_m, k, w, a, i + 1)
                == (Self::spec_win_exists_upto(h_c, d_c, h_m, d_m, k, w, a, i)
                    || Self::spec_player_wins(
                        Self::spec_effective_hp(h_c, k, a, i),
                        Self::spec_effective_attack(d_c, w, i),
                        h_m,
                        d_m,
                    )),
    {
        let lhs = Self::spec_win_exists_upto(h_c, d_c, h_m, d_m, k, w, a, i + 1);
        let rhs = Self::spec_win_exists_upto(h_c, d_c, h_m, d_m, k, w, a, i)
            || Self::spec_player_wins(
                Self::spec_effective_hp(h_c, k, a, i),
                Self::spec_effective_attack(d_c, w, i),
                h_m,
                d_m,
            );
        assert(lhs == rhs) by {
            if lhs {
                let u = choose|u: int|
                    0 <= u < i + 1 && Self::spec_player_wins(
                        Self::spec_effective_hp(h_c, k, a, u),
                        Self::spec_effective_attack(d_c, w, u),
                        h_m,
                        d_m,
                    );
                if u < i {
                    assert(Self::spec_win_exists_upto(h_c, d_c, h_m, d_m, k, w, a, i)) by {
                        let weapon_upgrades = u;
                        assert(0 <= weapon_upgrades < i);
                        assert(Self::spec_player_wins(
                            Self::spec_effective_hp(h_c, k, a, weapon_upgrades),
                            Self::spec_effective_attack(d_c, w, weapon_upgrades),
                            h_m,
                            d_m,
                        ));
                    };
                } else {
                    assert(u >= i);
                    assert(u < i + 1);
                    assert(u == i);
                    assert(Self::spec_player_wins(
                        Self::spec_effective_hp(h_c, k, a, i),
                        Self::spec_effective_attack(d_c, w, i),
                        h_m,
                        d_m,
                    ));
                }
                assert(rhs);
            }
            if rhs {
                if Self::spec_win_exists_upto(h_c, d_c, h_m, d_m, k, w, a, i) {
                    let u = choose|u: int|
                        0 <= u < i && Self::spec_player_wins(
                            Self::spec_effective_hp(h_c, k, a, u),
                            Self::spec_effective_attack(d_c, w, u),
                            h_m,
                            d_m,
                        );
                    assert(lhs) by {
                        let weapon_upgrades = u;
                        assert(0 <= weapon_upgrades < i + 1);
                        assert(Self::spec_player_wins(
                            Self::spec_effective_hp(h_c, k, a, weapon_upgrades),
                            Self::spec_effective_attack(d_c, w, weapon_upgrades),
                            h_m,
                            d_m,
                        ));
                    };
                } else {
                    assert(Self::spec_player_wins(
                        Self::spec_effective_hp(h_c, k, a, i),
                        Self::spec_effective_attack(d_c, w, i),
                        h_m,
                        d_m,
                    ));
                    assert(lhs) by {
                        let weapon_upgrades = i;
                        assert(0 <= weapon_upgrades < i + 1);
                        assert(Self::spec_player_wins(
                            Self::spec_effective_hp(h_c, k, a, weapon_upgrades),
                            Self::spec_effective_attack(d_c, w, weapon_upgrades),
                            h_m,
                            d_m,
                        ));
                    };
                }
            }
        };
    }

    fn player_wins_battle(hc: i64, dc: i64, hm: i64, dm: i64) -> (b: bool)
        requires
            1 <= hc <= 5_000_000_000_000_000,
            1 <= dc <= 5_000_000_000_000,
            1 <= hm <= 1_000_000_000_000_000,
            1 <= dm <= 1_000_000_000,
        ensures
            b == Self::spec_player_wins(hc as int, dc as int, hm as int, dm as int),
    {
        let hc128 = hc as i128;
        let dc128 = dc as i128;
        let hm128 = hm as i128;
        let dm128 = dm as i128;
        let strikes = 1 + (hm128 - 1) / dc128;
        let k = strikes - 1;
        let b = k <= (hc128 - 1) / dm128;
        proof {
            assert(strikes as int == 1 + (((hm as int) - 1) / (dc as int)));
            assert(strikes as int == Self::spec_ceil_div_pos(hm as int, dc as int));
            let kk = (strikes as int - 1);
            assert(kk == ((hm as int) - 1) / (dc as int));
            assert(kk >= 0);
            assert(k as int == kk);
            Self::lemma_int_win_cmp_div(hc as int, dm as int, kk);
            let spec_gt = hc as int > kk * (dm as int);
            let spec_div = kk <= ((hc as int) - 1) / (dm as int);
            assert(spec_gt == spec_div);
            assert(b == spec_div);
            assert(b == Self::spec_player_wins(hc as int, dc as int, hm as int, dm as int));
        }
        b
    }

    proof fn lemma_prefix_step(
        h_c: int,
        d_c: int,
        h_m: int,
        d_m: int,
        k: int,
        w: int,
        a: int,
        i: int,
        found_before: bool,
        win_i: bool,
        found_after: bool,
    )
        requires
            1 <= h_c,
            1 <= d_c,
            1 <= h_m,
            1 <= d_m,
            0 <= w,
            0 <= a,
            0 <= k,
            0 <= i <= k,
            found_before == Self::spec_win_exists_upto(h_c, d_c, h_m, d_m, k, w, a, i),
            win_i == Self::spec_player_wins(
                Self::spec_effective_hp(h_c, k, a, i),
                Self::spec_effective_attack(d_c, w, i),
                h_m,
                d_m,
            ),
            found_after == (found_before || win_i),
        ensures
            found_after == Self::spec_win_exists_upto(h_c, d_c, h_m, d_m, k, w, a, i + 1),
    {
        Self::lemma_win_exists_upto_succ(h_c, d_c, h_m, d_m, k, w, a, i);
        assert(found_after == Self::spec_win_exists_upto(h_c, d_c, h_m, d_m, k, w, a, i + 1));
    }

    pub fn can_slay_monster(
        h_c: i64,
        d_c: i64,
        h_m: i64,
        d_m: i64,
        k: i32,
        w: i32,
        a: i64,
    ) -> (r: bool)
        requires
            1 <= h_c <= 1_000_000_000_000_000,
            1 <= d_c <= 1_000_000_000,
            1 <= h_m <= 1_000_000_000_000_000,
            1 <= d_m <= 1_000_000_000,
            0 <= k <= 200_000,
            0 <= w <= 10_000,
            0 <= a <= 10_000_000_000,
        ensures
            r == Self::spec_can_slay(
                h_c as int,
                d_c as int,
                h_m as int,
                d_m as int,
                k as int,
                w as int,
                a as int,
            ),
    {
        let mut found = false;
        let mut i: i32 = 0;
        while i <= k
            invariant
                1 <= h_c <= 1_000_000_000_000_000,
                1 <= d_c <= 1_000_000_000,
                1 <= h_m <= 1_000_000_000_000_000,
                1 <= d_m <= 1_000_000_000,
                1 <= h_c as int <= 1_000_000_000_000_000,
                1 <= d_c as int <= 1_000_000_000,
                1 <= h_m as int <= 1_000_000_000_000_000,
                1 <= d_m as int <= 1_000_000_000,
                0 <= k <= 200_000,
                0 <= w <= 10_000,
                0 <= a <= 10_000_000_000,
                0 <= w as int <= 10_000,
                0 <= a as int <= 10_000_000_000,
                0 <= k as int <= 200_000,
                0 <= i <= k + 1,
                found == Self::spec_win_exists_upto(
                    h_c as int,
                    d_c as int,
                    h_m as int,
                    d_m as int,
                    k as int,
                    w as int,
                    a as int,
                    i as int,
                ),
            decreases k - i + 1,
        {
            let ghost found_before = found;
            let ki = (k - i) as i64;
            proof {
                assert(0 <= ki && ki <= 200_000);
                assert(ki * a <= 2_000_000_000_000_000) by (nonlinear_arith)
                    requires
                        0 <= ki <= 200_000,
                        0 <= a <= 10_000_000_000,
                ;
            }
            let hc_e = h_c + ki * a;
            let ii = i as i64;
            proof {
                assert(0 <= ii && ii <= 200_000);
                assert(ii * (w as i64) <= 2_000_000_000_000) by (nonlinear_arith)
                    requires
                        0 <= ii <= 200_000,
                        0 <= w <= 10_000,
                ;
            }
            let dc_e = d_c + ii * (w as i64);
            proof {
                assert((ki * a) as int == (ki as int) * (a as int));
                assert((ii * (w as i64)) as int == (ii as int) * (w as int));
                assert(hc_e as int == h_c as int + (ki as int) * (a as int));
                assert(dc_e as int == d_c as int + (ii as int) * (w as int));
                assert((ki as int) * (a as int) <= 2_000_000_000_000_000);
                assert((ii as int) * (w as int) <= 2_000_000_000_000);
                assert((ki as int) * (a as int) >= 0);
                assert((ii as int) * (w as int) >= 0);
                assert(1 <= hc_e as int) by (nonlinear_arith)
                    requires
                        hc_e as int == h_c as int + (ki as int) * (a as int),
                        1 <= h_c as int,
                        (ki as int) * (a as int) >= 0,
                ;
                assert(hc_e as int <= 5_000_000_000_000_000) by (nonlinear_arith)
                    requires
                        hc_e as int == h_c as int + (ki as int) * (a as int),
                        h_c as int <= 1_000_000_000_000_000,
                        (ki as int) * (a as int) <= 2_000_000_000_000_000,
                ;
                assert(1 <= dc_e as int) by (nonlinear_arith)
                    requires
                        dc_e as int == d_c as int + (ii as int) * (w as int),
                        1 <= d_c as int,
                        (ii as int) * (w as int) >= 0,
                ;
                assert(dc_e as int <= 5_000_000_000_000) by (nonlinear_arith)
                    requires
                        dc_e as int == d_c as int + (ii as int) * (w as int),
                        d_c as int <= 1_000_000_000,
                        (ii as int) * (w as int) <= 2_000_000_000_000,
                ;
            }
            let win_i = Self::player_wins_battle(hc_e, dc_e, h_m, d_m);
            proof {
                assert(Self::spec_effective_hp(h_c as int, k as int, a as int, i as int) == hc_e as int);
                assert(Self::spec_effective_attack(d_c as int, w as int, i as int) == dc_e as int);
                assert(win_i == Self::spec_player_wins(
                    Self::spec_effective_hp(h_c as int, k as int, a as int, i as int),
                    Self::spec_effective_attack(d_c as int, w as int, i as int),
                    h_m as int,
                    d_m as int,
                ));
            }
            if win_i {
                found = true;
            }
            proof {
                let found_after = found;
                Self::lemma_prefix_step(
                    h_c as int,
                    d_c as int,
                    h_m as int,
                    d_m as int,
                    k as int,
                    w as int,
                    a as int,
                    i as int,
                    found_before,
                    win_i,
                    found_after,
                );
            }
            i = i + 1;
        }
        proof {
            assert(i as int == k as int + 1);
            assert(found == Self::spec_win_exists_upto(
                h_c as int,
                d_c as int,
                h_m as int,
                d_m as int,
                k as int,
                w as int,
                a as int,
                k as int + 1,
            ));
            assert(found == Self::spec_can_slay(
                h_c as int,
                d_c as int,
                h_m as int,
                d_m as int,
                k as int,
                w as int,
                a as int,
            ));
        }
        found
    }
}

}
