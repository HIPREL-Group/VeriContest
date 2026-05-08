impl Solution {
    pub fn minimum_index(capacity: Vec<i32>, item_size: i32) -> i32 {
        let n = capacity.len();
        let mut i: usize = 0;
        let mut found: bool = false;
        let mut best_idx: usize = 0;
        let mut best_cap: i32 = 0;

        while i < n {
            let cap_i = capacity[i];
            if cap_i >= item_size {
                if !found {
                    found = true;
                    best_idx = i;
                    best_cap = cap_i;
                } else if cap_i < best_cap {
                    found = true;
                    best_idx = i;
                    best_cap = cap_i;
                }
            }
            i = i + 1;
        }

        if found {
            best_idx as i32
        } else {
            -1
        }
    }
}
