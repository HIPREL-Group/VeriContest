impl Solution {
    pub fn count_chat_times(
        z_starts: Vec<i32>,
        z_ends: Vec<i32>,
        x_starts: Vec<i32>,
        x_ends: Vec<i32>,
        l: i32,
        r: i32,
    ) -> i32 {
        let mut result = 0i32;
        let mut t = l;
        while t <= r {
            let mut found = false;
            let mut i = 0usize;
            while i < z_starts.len() && !found {
                let mut j = 0usize;
                while j < x_starts.len() && !found {
                    let zs = z_starts[i];
                    let ze = z_ends[i];
                    let xs = x_starts[j];
                    let xe = x_ends[j];
                    if xs + t <= ze && zs <= xe + t {
                        found = true;
                    } else {
                        j += 1;
                    }
                }
                if !found {
                    i += 1;
                }
            }
            if found {
                result += 1;
            }
            t += 1;
        }
        result
    }
}
