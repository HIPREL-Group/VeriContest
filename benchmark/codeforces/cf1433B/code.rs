impl Solution {
    pub fn min_moves_books(n: usize, a: Vec<u8>) -> usize {
        let mut first: usize = 0;
        let mut found_first = false;
        let mut i: usize = 0;
        while i < n {
            if a[i] == 1u8 && !found_first {
                first = i;
                found_first = true;
            }
            i += 1;
        }
        let mut last: usize = 0;
        let mut found_last = false;
        let mut j: usize = 0;
        while j < n {
            if a[j] == 1u8 {
                last = j;
                found_last = true;
            }
            j += 1;
        }
        if !found_first || !found_last {
            return 0;
        }
        let mut count: usize = 0;
        let mut k: usize = first;
        while k <= last {
            if a[k] == 0u8 {
                count += 1;
            }
            k += 1;
        }
        count
    }
}
