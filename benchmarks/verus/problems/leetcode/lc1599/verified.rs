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

    proof fn waiting_zero_lemma(customers: Seq<i32>, t: int, r: int)
        requires
            t >= 1,
            r >= t - 1,
            Self::waiting_after(customers, t - 1) == 0,
            t >= customers.len(),
        ensures
            Self::waiting_after(customers, r) == 0,
        decreases r - t + 1
    {
        if r > t - 1 {
            Self::waiting_zero_lemma(customers, t, r - 1);
        }
    }

    proof fn profit_bounded_lemma(customers: Seq<i32>, t: int, r: int, bc: int, rc: int, bound: int)
        requires
            t >= 1,
            r >= t,
            Self::waiting_after(customers, t - 1) == 0,
            t >= customers.len(),
            bc >= 1,
            rc >= 1,
            forall |k: int| 0 <= k < t ==>
                Self::cumul_profit(customers, k, bc, rc) <= bound,
        ensures
            Self::cumul_profit(customers, r, bc, rc) <= bound,
        decreases r - t
    {
        Self::waiting_zero_lemma(customers, t, r - 1);
        assert(Self::waiting_after(customers, r - 1) == 0);
        assert(Self::arrivals(customers, r) == 0);
        assert(Self::boarded_at(customers, r) == 0);
        if r > t {
            Self::profit_bounded_lemma(customers, t, r - 1, bc, rc, bound);
        } else {
            assert(Self::cumul_profit(customers, t - 1, bc, rc) <= bound);
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

        while i < n || waiting > 0
            invariant
                n == customers@.len(),
                1 <= n <= 100_000,
                bc as int == boarding_cost as int,
                rc as int == running_cost as int,
                1 <= bc <= 100,
                1 <= rc <= 100,
                forall |k: int| 0 <= k < n as int ==> 0 <= #[trigger] customers@[k] <= 50,
                0 <= i <= n,
                rotation >= 0,
                waiting >= 0,
                i as int == if rotation as int <= n as int { rotation as int } else { n as int },
                waiting as int == Self::waiting_after(customers@, rotation as int - 1),
                profit as int == Self::cumul_profit(customers@, rotation as int - 1, boarding_cost as int, running_cost as int),
                rotation as int + (n as int - i as int) * 51 + waiting as int <= 51 * n as int,
                profit >= -100 * rotation,
                profit <= 400 * rotation,
                max_profit >= 0,
                forall |r: int| 0 <= r < rotation as int ==>
                    Self::cumul_profit(customers@, r, boarding_cost as int, running_cost as int) <= max_profit as int,
                best_rotation == -1 || (1 <= best_rotation && best_rotation <= rotation),
                best_rotation == -1 ==> max_profit == 0,
                best_rotation > 0 ==>
                    max_profit as int == Self::cumul_profit(customers@, best_rotation as int - 1, boarding_cost as int, running_cost as int),
                best_rotation > 0 ==> max_profit > 0,
                best_rotation > 0 ==>
                    (forall |r: int| 0 <= r < best_rotation as int - 1 ==>
                        Self::cumul_profit(customers@, r, boarding_cost as int, running_cost as int) < max_profit as int),
            decreases (n as int - i as int) * 51 + waiting as int,
        {
            let ghost old_rotation = rotation;
            let ghost old_profit = profit;

            if i < n {
                waiting = waiting + customers[i] as i64;
                i = i + 1;
            }
            let board: i64 = if waiting >= 4 { 4 } else { waiting };

            proof {
                assert(0 <= board && board <= 4);
                assert(board * bc <= 400) by(nonlinear_arith)
                    requires 0 <= board <= 4, 1 <= bc <= 100 {};
                assert(board * bc >= 0) by(nonlinear_arith)
                    requires 0 <= board, 1 <= bc {};
            }

            waiting = waiting - board;
            profit = profit + board * bc - rc;
            rotation = rotation + 1;

            proof {
                assert(profit >= -100 * rotation) by {
                    assert(old_profit >= -100 * old_rotation);
                    assert(board * bc >= 0);
                    assert(rc <= 100);
                }
                assert(profit <= 400 * rotation) by {
                    assert(old_profit <= 400 * old_rotation);
                    assert(board * bc <= 400);
                    assert(rc >= 1);
                }
            }

            if profit > max_profit {
                max_profit = profit;
                best_rotation = rotation;
            }
        }

        proof {
            assert(rotation as int >= n as int);
            assert(waiting as int == 0);
            assert(Self::waiting_after(customers@, rotation as int - 1) == 0);

            assert forall |r: int| 0 <= r implies
                Self::cumul_profit(customers@, r, boarding_cost as int, running_cost as int) <= max_profit as int by {
                if r < rotation as int {
                } else {
                    Self::profit_bounded_lemma(
                        customers@, rotation as int, r, boarding_cost as int, running_cost as int, max_profit as int
                    );
                }
            };
        }

        best_rotation as i32
    }
}

}

