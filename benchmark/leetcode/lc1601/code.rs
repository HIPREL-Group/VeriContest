impl Solution {
    pub fn maximum_requests(n: i32, requests: Vec<Vec<i32>>) -> i32 {
        let m = requests.len();
        let mut total: u32 = 1;
        let mut p: usize = 0;
        while p < m {
            total = total * 2;
            p += 1;
        }
        let mut net: Vec<i32> = Vec::new();
        let mut init_k: usize = 0;
        while init_k < n as usize {
            net.push(0i32);
            init_k += 1;
        }
        let mut best: i32 = 0;
        let mut mask: u32 = 0;
        while mask < total {
            let mut r: usize = 0;
            while r < n as usize {
                net[r] = 0i32;
                r += 1;
            }
            let mut count: i32 = 0;
            let mut j: usize = 0;
            let mut pow_j: u32 = 1;
            while j < m {
                if (mask / pow_j) % 2 == 1 {
                    let from_b = requests[j][0] as usize;
                    let to_b = requests[j][1] as usize;
                    let old_from = net[from_b];
                    net[from_b] = old_from - 1;
                    let cur_to = net[to_b];
                    net[to_b] = cur_to + 1;
                    count += 1;
                }
                pow_j = pow_j * 2;
                j += 1;
            }
            let mut balanced: bool = true;
            let mut k: usize = 0;
            while k < n as usize {
                if net[k] != 0 {
                    balanced = false;
                }
                k += 1;
            }
            if balanced && count > best {
                best = count;
            }
            mask += 1;
        }
        best
    }
}
