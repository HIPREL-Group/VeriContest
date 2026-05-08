impl Solution {
    pub fn min_operations_max_profit(customers: Vec<i32>, boarding_cost: i32, running_cost: i32) -> i32 {
        let n = customers.len();
        let bc = boarding_cost as i64;
        let rc = running_cost as i64;
        let mut i: usize = 0;
        let mut waiting: i64 = 0;
        let mut profit: i64 = 0;
        let mut max_profit: i64 = 0;
        let mut best_rotation: i64 = -1;
        let mut rotation: i64 = 0;

        while i < n || waiting > 0 {
            if i < n {
                waiting = waiting + customers[i] as i64;
                i = i + 1;
            }
            let board: i64 = if waiting >= 4 { 4 } else { waiting };
            waiting = waiting - board;
            profit = profit + board * bc - rc;
            rotation = rotation + 1;
            if profit > max_profit {
                max_profit = profit;
                best_rotation = rotation;
            }
        }

        best_rotation as i32
    }
}
