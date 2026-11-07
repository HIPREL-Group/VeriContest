impl Solution {
    fn add_mod(x: i32, y: i32) -> i32 {
        let sum = x + y;
        if sum >= 1_000_000_007i32 {
            sum - 1_000_000_007i32
        } else {
            sum
        }
    }

    pub fn count_k_tree_paths(n: i32, k: i32, d: i32) -> i32 {
        let mut no_large = Vec::new();
        no_large.push(1);
        let mut has_large = Vec::new();
        has_large.push(0);
        let mut total = 1usize;
        while total <= n as usize {
            let current = total;
            let upper = if current < k as usize { current } else { k as usize };
            let mut small = 0i32;
            let mut large = 0i32;
            let mut step = 1usize;
            while step <= upper {
                let prev_small = no_large[current - step];
                let prev_large = has_large[current - step];
                if step < d as usize {
                    small = Self::add_mod(small, prev_small);
                    large = Self::add_mod(large, prev_large);
                } else {
                    large = Self::add_mod(large, prev_small);
                    large = Self::add_mod(large, prev_large);
                }
                step += 1;
            }
            no_large.push(small);
            has_large.push(large);
            total += 1;
        }
        has_large[n as usize]
    }
}
