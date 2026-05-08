impl Solution {
    pub fn gcd(a: u64, b: u64) -> u64 {
        let mut x = a;
        let mut y = b;
        while y != 0 {
            let t = y;
            y = x % y;
            x = t;
        }
        x
    }

    pub fn min_tags(a: Vec<i64>, b: Vec<i64>) -> u64 {
        let n = a.len();
        if n == 0 {
            return 0;
        }

        let mut closed: u64 = 0;
        let mut cur_lcm: u64 = b[0] as u64;
        let mut cur_gcd: u64 = (a[0] as u64) * (b[0] as u64);
        let mut i: usize = 1;

        while i < n {
            let aval = a[i] as u64;
            let bval = b[i] as u64;

            let g = Self::gcd(cur_lcm, bval);
            if g > 0 {
                let q = cur_lcm / g;
                if q <= 18_446_744_073_709_551_615u64 / bval {
                    let next_lcm = q * bval;
                    let next_gcd = Self::gcd(cur_gcd, aval * bval);

                    if next_lcm > 0 && next_gcd % next_lcm == 0 {
                        cur_lcm = next_lcm;
                        cur_gcd = next_gcd;
                    } else {
                        closed = closed + 1;
                        cur_lcm = bval;
                        cur_gcd = aval * bval;
                    }
                } else {
                    closed = closed + 1;
                    cur_lcm = bval;
                    cur_gcd = aval * bval;
                }
            } else {
                closed = closed + 1;
                cur_lcm = bval;
                cur_gcd = aval * bval;
            }
            i = i + 1;
        }
        closed + 1
    }
}
