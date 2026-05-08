use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_bill_prefix(bills: Seq<i32>, n: nat, bill: i32) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        count_bill_prefix(bills, (n - 1) as nat, bill) + if bills[(n - 1) as int] == bill { 1int } else { 0int }
    }
}

pub open spec fn remaining_fives(bills: Seq<i32>, n: nat, used_ten: int) -> int {
    count_bill_prefix(bills, n, 5) - count_bill_prefix(bills, n, 10) - 3 * count_bill_prefix(bills, n, 20) + 2 * used_ten
}

pub open spec fn remaining_tens(bills: Seq<i32>, n: nat, used_ten: int) -> int {
    count_bill_prefix(bills, n, 10) - used_ten
}

pub open spec fn possible_state(bills: Seq<i32>, n: nat, used_ten: int) -> bool
    decreases n
{
    if n == 0 {
        used_ten == 0
    } else if bills[(n - 1) as int] == 5 {
        possible_state(bills, (n - 1) as nat, used_ten)
    } else if bills[(n - 1) as int] == 10 {
        possible_state(bills, (n - 1) as nat, used_ten) && remaining_fives(bills, (n - 1) as nat, used_ten) >= 1
    } else {
        (used_ten >= 1 && possible_state(bills, (n - 1) as nat, used_ten - 1) && remaining_fives(bills, (n - 1) as nat, used_ten - 1) >= 1 && remaining_tens(bills, (n - 1) as nat, used_ten - 1) >= 1)
        || (possible_state(bills, (n - 1) as nat, used_ten) && remaining_fives(bills, (n - 1) as nat, used_ten) >= 3)
    }
}

pub open spec fn prefix_possible(bills: Seq<i32>, n: nat) -> bool {
    exists |used_ten: int| possible_state(bills, n, used_ten)
}

pub open spec fn can_make_change(bills: Seq<i32>) -> bool {
    prefix_possible(bills, bills.len())
}

impl Solution {
    pub fn lemonade_change(bills: Vec<i32>) -> (res: bool)
        requires
            1 <= bills.len() <= 100_000,
            forall |i: int| 0 <= i < bills.len() ==> bills[i] == 5 || bills[i] == 10 || bills[i] == 20,
        ensures
            res == can_make_change(bills@),
    {
        let mut five: usize = 0;
        let mut ten: usize = 0;
        let mut used_ten: usize = 0;
        let mut i: usize = 0;
        while i < bills.len() {
            let bill = bills[i];
            if bill == 5 {
                five = five + 1;
            } else if bill == 10 {
                if five == 0 {
                    return false;
                }
                five = five - 1;
                ten = ten + 1;
            } else {
                if ten > 0 && five > 0 {
                    ten = ten - 1;
                    five = five - 1;
                    used_ten = used_ten + 1;
                } else if five >= 3 {
                    five = five - 3;
                } else {
                    return false;
                }
            }
            i = i + 1;
        }
        true
    }
}

}
