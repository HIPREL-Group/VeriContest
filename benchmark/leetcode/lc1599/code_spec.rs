use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn arrivals(customers: Seq<i32>, r: int) -> int {
        if 0 <= r < customers.len() { customers[r] as int } else { 0 }
    }

    pub open spec fn waiting_after(customers: Seq<i32>, r: int) -> int
        decreases r
    {
        if r < 0 {
            0
        } else if r == 0 {
            let available = Self::arrivals(customers, 0);
            if available >= 4 { available - 4 } else { 0 }
        } else {
            let available = Self::waiting_after(customers, r - 1) + Self::arrivals(customers, r);
            if available >= 4 { available - 4 } else { 0 }
        }
    }

    pub open spec fn boarded_at(customers: Seq<i32>, r: int) -> int {
        if r < 0 {
            0
        } else {
            let available = (if r == 0 { 0 } else { Self::waiting_after(customers, r - 1) })
                + Self::arrivals(customers, r);
            if available >= 4 { 4 } else { available }
        }
    }

    pub open spec fn cumul_profit(customers: Seq<i32>, r: int, bc: int, rc: int) -> int
        decreases r
    {
        if r < 0 {
            0
        } else if r == 0 {
            Self::boarded_at(customers, 0) * bc - rc
        } else {
            Self::cumul_profit(customers, r - 1, bc, rc) + Self::boarded_at(customers, r) * bc - rc
        }
    }

    pub fn min_operations_max_profit(customers: Vec<i32>, boarding_cost: i32, running_cost: i32) -> (res: i32)
        requires
            1 <= customers.len() <= 100_000,
            forall |i: int| 0 <= i < customers.len() ==> 0 <= #[trigger] customers[i] <= 50,
            1 <= boarding_cost <= 100,
            1 <= running_cost <= 100,
        ensures
            res == -1 || res >= 1,
            res > 0 ==>
                Self::cumul_profit(customers@, res as int - 1, boarding_cost as int, running_cost as int) > 0,
            res > 0 ==>
                (forall |r: int| 0 <= r ==>
                    #[trigger] Self::cumul_profit(customers@, r, boarding_cost as int, running_cost as int) <=
                    Self::cumul_profit(customers@, res as int - 1, boarding_cost as int, running_cost as int)),
            res > 0 ==>
                (forall |r: int| 0 <= r < res as int - 1 ==>
                    #[trigger] Self::cumul_profit(customers@, r, boarding_cost as int, running_cost as int) <
                    Self::cumul_profit(customers@, res as int - 1, boarding_cost as int, running_cost as int)),
            res == -1 ==>
                (forall |r: int| 0 <= r ==>
                    #[trigger] Self::cumul_profit(customers@, r, boarding_cost as int, running_cost as int) <= 0),
    {
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

}
