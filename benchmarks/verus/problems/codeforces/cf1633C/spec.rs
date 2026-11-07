use vstd::prelude::*;

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
    }
}

}
