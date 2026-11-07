impl Solution {
    pub fn maximum_points(enemy_energies: Vec<i32>, current_energy: i32) -> i64 {
        let n = enemy_energies.len();
        let mut i = 0usize;
        let mut min_energy = enemy_energies[0] as i64;
        let mut total_energy = current_energy as i64;

        while i < n {
            let x = enemy_energies[i] as i64;
            if x < min_energy {
                min_energy = x;
            }
            total_energy = total_energy.checked_add(x).unwrap_or(total_energy);
            i += 1;
        }

        if (current_energy as i64) < min_energy {
            return 0;
        }

        total_energy = total_energy.checked_sub(min_energy).unwrap_or(total_energy);
        if min_energy <= 0 || total_energy <= 0 {
            return 0;
        }
        let ans = total_energy / min_energy;
        if ans < 0 { 0 } else { ans }
    }
}
