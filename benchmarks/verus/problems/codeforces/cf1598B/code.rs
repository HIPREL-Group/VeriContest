impl Solution {
    pub fn groups(n: usize, days: Vec<Vec<bool>>) -> bool {
        let mut found = false;
        let mut d1: usize = 0;
        while d1 < 5 && !found {
            let mut d2: usize = d1 + 1;
            while d2 < 5 && !found {
                let mut either: usize = 0;
                let mut can_d1: usize = 0;
                let mut can_d2: usize = 0;
                let mut i: usize = 0;
                while i < n {
                    let c1 = days[i][d1];
                    let c2 = days[i][d2];
                    if c1 || c2 {
                        either += 1;
                    }
                    if c1 {
                        can_d1 += 1;
                    }
                    if c2 {
                        can_d2 += 1;
                    }
                    i += 1;
                }
                
                if either == n && can_d1 >= n / 2 && can_d2 >= n / 2 {
                    found = true;
                }
                d2 += 1;
            }
            d1 += 1;
        }
        found
    }
}
