impl Solution {
    pub fn construct_array(n: i32, k: i32) -> Vec<i32>
    {
        let mut result = Vec::new();
        let mut i: usize = 0;
        while i < n as usize
        {
            result.push(0);
            i += 1;
        }

        let mut idx: usize = 0;
        while idx <= k as usize
        {
            let val = if idx % 2 == 0 {
                1 + (idx as i32) / 2
            } else {
                (k + 1) - ((idx as i32) - 1) / 2
            };
            result[idx] = val;
            idx += 1;
        }

        let mut idx2 = idx;
        while idx2 < n as usize
        {
            result[idx2] = (idx2 as i32) + 1;
            idx2 += 1;
        }

        result
    }
}
