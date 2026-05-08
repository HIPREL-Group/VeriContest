use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn i64_min() -> int {
        -9223372036854775808
    }

    pub open spec fn i64_max() -> int {
        9223372036854775807
    }

    pub open spec fn checked_add_or(a: int, b: int, fallback: int) -> int {
        let s = a + b;
        if Self::i64_min() <= s <= Self::i64_max() { s } else { fallback }
    }

    pub open spec fn checked_sub_or(a: int, b: int, fallback: int) -> int {
        let s = a - b;
        if Self::i64_min() <= s <= Self::i64_max() { s } else { fallback }
    }

    pub open spec fn min_scanned(enemy_energies: Seq<i32>, i: int) -> int
        decreases if i > 0 { i } else { 0 },
    {
        if enemy_energies.len() == 0 {
            0
        } else if i <= 0 {
            enemy_energies[0] as int
        } else {
            let prev = Self::min_scanned(enemy_energies, i - 1);
            let x = enemy_energies[i - 1] as int;
            if x < prev { x } else { prev }
        }
    }

    pub open spec fn total_scanned(enemy_energies: Seq<i32>, current_energy: int, i: int) -> int
        decreases if i > 0 { i } else { 0 },
    {
        if i <= 0 {
            current_energy
        } else {
            let prev = Self::total_scanned(enemy_energies, current_energy, i - 1);
            Self::checked_add_or(prev, enemy_energies[i - 1] as int, prev)
        }
    }

    pub open spec fn maximum_points_spec(enemy_energies: Seq<i32>, current_energy: i32, result: int) -> bool {
        &&& 1 <= enemy_energies.len() <= 100000
        &&& 0 <= current_energy <= 1000000000
        &&& forall |i: int| 0 <= i < enemy_energies.len() ==> 1 <= #[trigger] enemy_energies[i] <= 1000000000
        &&& {
            let n = enemy_energies.len() as int;
            let min_energy = Self::min_scanned(enemy_energies, n);
            let total_energy = Self::total_scanned(enemy_energies, current_energy as int, n);
            if (current_energy as int) < min_energy {
                result == 0
            } else {
                let rem = Self::checked_sub_or(total_energy, min_energy, total_energy);
                if min_energy <= 0 || rem <= 0 {
                    result == 0
                } else {
                    let ans = rem / min_energy;
                    if ans < 0 { result == 0 } else { result == (ans as i64) as int }
                }
            }
        }
    }

    pub fn maximum_points(enemy_energies: Vec<i32>, current_energy: i32) -> (result: i64)
        requires
            1 <= enemy_energies.len() <= 100000,
            0 <= current_energy <= 1000000000,
            forall |i: int| 0 <= i < enemy_energies.len() ==> 1 <= #[trigger] enemy_energies[i] <= 1000000000,
        ensures
            Self::maximum_points_spec(enemy_energies@, current_energy, result as int),
    {
    }
}

}
