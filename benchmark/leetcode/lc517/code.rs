impl Solution {
    pub fn find_min_moves(machines: Vec<i32>) -> i32 {
        let n = machines.len();
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            total = total + machines[i] as i64;
            i += 1;
        }

        if total % n as i64 != 0 {
            return -1;
        }

        let avg = total / n as i64;
        let mut balance: i64 = 0;
        let mut res: i64 = 0;
        i = 0;
        while i < n {
            let diff = machines[i] as i64 - avg;
            balance = balance + diff;
            let abs_bal = if balance >= 0 { balance } else { -balance };
            let need = if abs_bal >= diff { abs_bal } else { diff };
            res = if res >= need { res } else { need };
            i += 1;
        }

        res as i32
    }
}
