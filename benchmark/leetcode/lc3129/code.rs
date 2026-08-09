impl Solution {
    pub fn number_of_stable_arrays(zero: i32, one: i32, limit: i32) -> i32 {
        let zu: usize = zero as usize;
        let ou: usize = one as usize;
        let limu: usize = limit as usize;
        let md: i64 = 1000000007;

        let mut ways0: Vec<Vec<i64>> = Vec::new();
        let mut ways1: Vec<Vec<i64>> = Vec::new();

        let mut z: usize = 0;
        while z <= zu {
            let mut row0: Vec<i64> = Vec::new();
            let mut row1: Vec<i64> = Vec::new();
            let mut o: usize = 0;
            while o <= ou {
                if z == 0 && o == 0 {
                    row0.push(1);
                    row1.push(1);
                } else {
                    let upto0: usize = if z <= limu { z } else { limu };
                    let mut s0: i64 = 0;
                    let mut u: usize = 1;
                    while u <= upto0 {
                        let idx0: usize = z - u;
                        let term_val: i64 = ways1[idx0][o];
                        s0 = (s0 + term_val) % md;
                        u += 1;
                    }
                    row0.push(s0);

                    let upto1: usize = if o <= limu { o } else { limu };
                    let mut s1: i64 = 0;
                    let mut u2: usize = 1;
                    while u2 <= upto1 {
                        let idx1: usize = o - u2;
                        let term_val1: i64 = row0[idx1];
                        s1 = (s1 + term_val1) % md;
                        u2 += 1;
                    }
                    row1.push(s1);
                }
                o += 1;
            }
            ways0.push(row0);
            ways1.push(row1);
            z += 1;
        }

        let a = ways0[zu][ou];
        let b = ways1[zu][ou];
        let result = ((a + b) % md) as i32;
        result
    }
}
