impl Solution {
    pub fn stone_game_vi(alice_values: Vec<i32>, bob_values: Vec<i32>) -> i32 {
        let n = alice_values.len();
        let mut indices: Vec<usize> = Vec::new();
        let mut v: usize = 200;
        while v >= 2 {
            let mut i: usize = 0;
            while i < n {
                if alice_values[i] + bob_values[i] == v as i32 {
                    indices.push(i);
                }
                i += 1;
            }
            v -= 1;
        }
        let mut alice_total: i32 = 0;
        let mut bob_total: i32 = 0;
        let mut k: usize = 0;
        while k < n {
            if k % 2 == 0 {
                alice_total += alice_values[indices[k]];
            } else {
                bob_total += bob_values[indices[k]];
            }
            k += 1;
        }
        if alice_total > bob_total {
            1
        } else if alice_total < bob_total {
            -1
        } else {
            0
        }
    }
}
