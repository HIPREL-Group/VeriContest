impl Solution {
    pub fn count_untreated(n: usize, events: Vec<i32>) -> u64 {
        let mut officers: u64 = 0;
        let mut untreated: u64 = 0;
        let mut i: usize = 0;
        while i < n {
            let e = events[i];
            if e == -1 {
                if officers > 0 {
                    officers = officers - 1;
                } else {
                    untreated = untreated + 1;
                }
            } else {
                officers = officers + (e as u64);
            }
            i += 1;
        }
        untreated
    }
}
