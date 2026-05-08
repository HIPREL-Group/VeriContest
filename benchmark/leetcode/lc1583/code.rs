impl Solution {
    pub fn unhappy_friends(n: i32, preferences: Vec<Vec<i32>>, pairs: Vec<Vec<i32>>) -> i32 {
        let mut rank: Vec<i32> = Vec::new();
        let mut idx = 0;
        while idx < n * n {
            rank.push(0);
            idx = idx + 1;
        }
        let mut i = 0;
        while i < n {
            let mut j = 0;
            while j < n - 1 {
                let p = preferences[i as usize][j as usize];
                rank[(i * n + p) as usize] = j;
                j = j + 1;
            }
            i = i + 1;
        }
        let mut partner: Vec<i32> = Vec::new();
        idx = 0;
        while idx < n {
            partner.push(0);
            idx = idx + 1;
        }
        let mut k = 0;
        while k < n / 2 {
            let a = pairs[k as usize][0];
            let b = pairs[k as usize][1];
            partner[a as usize] = b;
            partner[b as usize] = a;
            k = k + 1;
        }
        let mut count = 0;
        i = 0;
        while i < n {
            let mut u = 0;
            let mut found = false;
            while u < n && !found {
                if u != i {
                    if rank[(i * n + u) as usize] < rank[(i * n + partner[i as usize]) as usize]
                        && rank[(u * n + i) as usize] < rank[(u * n + partner[u as usize]) as usize]
                    {
                        found = true;
                    }
                }
                u = u + 1;
            }
            if found {
                count = count + 1;
            }
            i = i + 1;
        }
        count
    }
}
