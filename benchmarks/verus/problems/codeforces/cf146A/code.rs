impl Solution {
    pub fn is_lucky_ticket(n: usize, digits: Vec<u8>) -> bool {
        let mut all_lucky = true;
        let mut i: usize = 0;
        while i < n {
            if digits[i] != 4u8 && digits[i] != 7u8 {
                all_lucky = false;
            }
            i += 1;
        }
        if !all_lucky {
            return false;
        }
        let half = n / 2;
        let mut sum1: u64 = 0;
        let mut sum2: u64 = 0;
        let mut j: usize = 0;
        while j < half {
            sum1 = sum1 + digits[j] as u64;
            j += 1;
        }
        let mut k: usize = half;
        while k < n {
            sum2 = sum2 + digits[k] as u64;
            k += 1;
        }
        sum1 == sum2
    }
}
