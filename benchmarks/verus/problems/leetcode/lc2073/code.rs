impl Solution {
    pub fn time_required_to_buy(tickets: Vec<i32>, k: i32) -> i32 {
        let n = tickets.len();
        let kk = k as usize;
        let target = tickets[kk];
        let mut total = 0;
        let mut i: usize = 0;

        while i < n {
            let buy = if i <= kk { target } else { target - 1 };
            if tickets[i] < buy {
                total = total + tickets[i];
            } else {
                total = total + buy;
            }
            i = i + 1;
        }

        total
    }
}
