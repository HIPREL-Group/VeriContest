impl Solution {
    pub fn count_largest_group(n: i32) -> i32 {
        let mut counts: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < 37
        {
            counts.push(0);
            k = k + 1;
        }
        let mut i: i32 = 1;
        while i <= n
        {
            let mut ds: i32 = 0;
            let mut x: i32 = i;
            while x > 0
            {
                ds = ds + (x % 10) as i32;
                x = x / 10;
            }
            counts[ds as usize] = counts[ds as usize] + 1;
            i = i + 1;
        }
        let mut max_size: i32 = 0;
        let mut count: i32 = 0;
        let mut j: usize = 1;
        while j < 37
        {
            if counts[j] > max_size {
                max_size = counts[j];
                count = 1;
            } else if counts[j] == max_size && max_size > 0 {
                count = count + 1;
            }
            j = j + 1;
        }
        count
    }
}