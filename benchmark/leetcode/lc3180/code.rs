impl Solution {
    pub fn max_total_reward(reward_values: Vec<i32>) -> i32 {
        if reward_values.len() == 1 {
            return reward_values[0];
        }
        let mut vals = reward_values.clone();
        let mut a = 1usize;
        while a < vals.len() {
            let key = vals[a];
            let mut b = a;
            while b > 0 && vals[b - 1] > key {
                vals[b] = vals[b - 1];
                b -= 1;
            }
            vals[b] = key;
            a += 1;
        }

        let mut reachable: Vec<bool> = vec![false; 4001];
        reachable[0] = true;

        let mut i = 0usize;
        while i < vals.len() {
            let r = vals[i] as usize;
            let mut s = 4000usize;
            loop {
                if reachable[s] && s < r {
                    let t = s + r;
                    if t <= 4000 {
                        reachable[t] = true;
                    }
                }
                if s == 0 {
                    break;
                }
                s -= 1;
            }
            i += 1;
        }

        let mut ans = 0usize;
        let mut x = 0usize;
        while x <= 4000 {
            if reachable[x] {
                ans = x;
            }
            if x == 4000 {
                break;
            }
            x += 1;
        }
        ans as i32
    }
}
