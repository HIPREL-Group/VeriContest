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

proof fn lemma_count_bill_prefix_step(bills: Seq<i32>, n: nat, bill: i32)
    requires
        n < bills.len(),
    ensures
        count_bill_prefix(bills, n + 1, bill) == count_bill_prefix(bills, n, bill) + if bills[n as int] == bill { 1int } else { 0int },
{
    reveal_with_fuel(count_bill_prefix, 2);
}

proof fn lemma_step_bill_5(bills: Seq<i32>, n: nat, used_ten: int)
    requires
        n < bills.len(),
        bills[n as int] == 5,
    ensures
        remaining_fives(bills, n + 1, used_ten) == remaining_fives(bills, n, used_ten) + 1,
        remaining_tens(bills, n + 1, used_ten) == remaining_tens(bills, n, used_ten),
{
    lemma_count_bill_prefix_step(bills, n, 5);
    lemma_count_bill_prefix_step(bills, n, 10);
}

proof fn lemma_step_bill_10(bills: Seq<i32>, n: nat, used_ten: int)
    requires
        n < bills.len(),
        bills[n as int] == 10,
    ensures
        remaining_fives(bills, n + 1, used_ten) == remaining_fives(bills, n, used_ten) - 1,
        remaining_tens(bills, n + 1, used_ten) == remaining_tens(bills, n, used_ten) + 1,
{
    lemma_count_bill_prefix_step(bills, n, 5);
    lemma_count_bill_prefix_step(bills, n, 10);
}

proof fn lemma_step_bill_20_use_ten(bills: Seq<i32>, n: nat, used_ten: int)
    requires
        n < bills.len(),
        bills[n as int] == 20,
    ensures
        remaining_fives(bills, n + 1, used_ten + 1) == remaining_fives(bills, n, used_ten) - 1,
        remaining_tens(bills, n + 1, used_ten + 1) == remaining_tens(bills, n, used_ten) - 1,
{
    lemma_count_bill_prefix_step(bills, n, 5);
    lemma_count_bill_prefix_step(bills, n, 10);
    lemma_count_bill_prefix_step(bills, n, 20);
}

proof fn lemma_step_bill_20_use_fives(bills: Seq<i32>, n: nat, used_ten: int)
    requires
        n < bills.len(),
        bills[n as int] == 20,
    ensures
        remaining_fives(bills, n + 1, used_ten) == remaining_fives(bills, n, used_ten) - 3,
        remaining_tens(bills, n + 1, used_ten) == remaining_tens(bills, n, used_ten),
{
    lemma_count_bill_prefix_step(bills, n, 5);
    lemma_count_bill_prefix_step(bills, n, 10);
    lemma_count_bill_prefix_step(bills, n, 20);
}

proof fn lemma_tens_positive_implies_fives_smaller(bills: Seq<i32>, n: nat, u: int, used_ten: int)
    requires
        remaining_tens(bills, n, used_ten) == 0,
        remaining_tens(bills, n, u) >= 1,
    ensures
        remaining_fives(bills, n, u) <= remaining_fives(bills, n, used_ten) - 2,
{
}

proof fn lemma_prefix_possible_of_longer_prefix(bills: Seq<i32>, m: nat, n: nat)
    requires
        m <= n <= bills.len(),
        prefix_possible(bills, n),
    ensures
        prefix_possible(bills, m),
    decreases n - m,
{
    if m < n {
        let used_ten = choose |used_ten: int| possible_state(bills, n, used_ten);
        reveal_with_fuel(possible_state, 2);
        if bills[(n - 1) as int] == 5 {
            assert(prefix_possible(bills, (n - 1) as nat)) by {
                assert(possible_state(bills, (n - 1) as nat, used_ten));
            }
        } else if bills[(n - 1) as int] == 10 {
            assert(prefix_possible(bills, (n - 1) as nat)) by {
                assert(possible_state(bills, (n - 1) as nat, used_ten));
            }
        } else {
            if used_ten >= 1 && possible_state(bills, (n - 1) as nat, used_ten - 1) && remaining_fives(bills, (n - 1) as nat, used_ten - 1) >= 1 && remaining_tens(bills, (n - 1) as nat, used_ten - 1) >= 1 {
                assert(prefix_possible(bills, (n - 1) as nat)) by {
                    assert(possible_state(bills, (n - 1) as nat, used_ten - 1));
                }
            } else {
                assert(prefix_possible(bills, (n - 1) as nat)) by {
                    assert(possible_state(bills, (n - 1) as nat, used_ten));
                }
            }
        }
        lemma_prefix_possible_of_longer_prefix(bills, m, (n - 1) as nat);
    }
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
        while i < bills.len()
            invariant
                1 <= bills.len() <= 100_000,
                forall |j: int| 0 <= j < bills.len() ==> bills[j] == 5 || bills[j] == 10 || bills[j] == 20,
                0 <= i <= bills.len(),
                five <= i,
                ten <= i,
                used_ten <= i,
                possible_state(bills@, i as nat, used_ten as int),
                five as int == remaining_fives(bills@, i as nat, used_ten as int),
                ten as int == remaining_tens(bills@, i as nat, used_ten as int),
                forall |u: int| (#[trigger] possible_state(bills@, i as nat, u)) ==> u <= used_ten as int,
                forall |u: int| (#[trigger] possible_state(bills@, i as nat, u)) ==> remaining_fives(bills@, i as nat, u) <= five as int,
            decreases bills.len() - i,
        {
            let bill = bills[i];
            let ghost old_i = i as nat;
            let ghost old_used_ten = used_ten as int;
            let ghost old_five = five as int;
            let ghost old_ten = ten as int;

            if bill == 5 {
                five = five + 1;
                proof {
                    assert(bills@[old_i as int] == 5);
                    lemma_step_bill_5(bills@, old_i, old_used_ten);
                    assert(five as int == old_five + 1);
                    assert(possible_state(bills@, old_i + 1, old_used_ten));
                    assert forall |u: int| (#[trigger] possible_state(bills@, old_i + 1, u)) implies u <= used_ten as int by {
                        assert(possible_state(bills@, old_i, u));
                    };
                    assert forall |u: int| (#[trigger] possible_state(bills@, old_i + 1, u)) implies remaining_fives(bills@, old_i + 1, u) <= five as int by {
                        lemma_step_bill_5(bills@, old_i, u);
                        assert(possible_state(bills@, old_i, u));
                        assert(remaining_fives(bills@, old_i, u) <= old_five);
                    };
                }
            } else if bill == 10 {
                if five == 0 {
                    proof {
                        assert(bills@[old_i as int] == 10);
                        assert forall |u: int| !(#[trigger] possible_state(bills@, old_i + 1, u)) by {
                            reveal_with_fuel(possible_state, 2);
                            if possible_state(bills@, old_i + 1, u) {
                                assert(possible_state(bills@, old_i, u));
                                assert(remaining_fives(bills@, old_i, u) >= 1);
                                assert(remaining_fives(bills@, old_i, u) <= old_five);
                            }
                        };
                        assert(!prefix_possible(bills@, old_i + 1));
                        assert(!can_make_change(bills@)) by {
                            if can_make_change(bills@) {
                                lemma_prefix_possible_of_longer_prefix(bills@, old_i + 1, bills.len() as nat);
                            }
                        };
                    }
                    return false;
                }
                five = five - 1;
                ten = ten + 1;
                proof {
                    assert(bills@[old_i as int] == 10);
                    lemma_step_bill_10(bills@, old_i, old_used_ten);
                    assert(possible_state(bills@, old_i + 1, old_used_ten));
                    assert forall |u: int| (#[trigger] possible_state(bills@, old_i + 1, u)) implies u <= used_ten as int by {
                        reveal_with_fuel(possible_state, 2);
                        assert(possible_state(bills@, old_i, u));
                    };
                    assert forall |u: int| (#[trigger] possible_state(bills@, old_i + 1, u)) implies remaining_fives(bills@, old_i + 1, u) <= five as int by {
                        reveal_with_fuel(possible_state, 2);
                        lemma_step_bill_10(bills@, old_i, u);
                        assert(possible_state(bills@, old_i, u));
                        assert(remaining_fives(bills@, old_i, u) <= old_five);
                    };
                }
            } else {
                if ten > 0 && five > 0 {
                    ten = ten - 1;
                    five = five - 1;
                    used_ten = used_ten + 1;
                    proof {
                        assert(bills@[old_i as int] == 20);
                        lemma_step_bill_20_use_ten(bills@, old_i, old_used_ten);
                        assert(possible_state(bills@, old_i + 1, old_used_ten + 1));
                        assert forall |u: int| (#[trigger] possible_state(bills@, old_i + 1, u)) implies u <= used_ten as int by {
                            reveal_with_fuel(possible_state, 2);
                            if u >= 1 && possible_state(bills@, old_i, u - 1) && remaining_fives(bills@, old_i, u - 1) >= 1 && remaining_tens(bills@, old_i, u - 1) >= 1 {
                                assert(u - 1 <= old_used_ten);
                            } else {
                                assert(possible_state(bills@, old_i, u));
                                assert(u <= old_used_ten);
                            }
                        };
                        assert forall |u: int| (#[trigger] possible_state(bills@, old_i + 1, u)) implies remaining_fives(bills@, old_i + 1, u) <= five as int by {
                            reveal_with_fuel(possible_state, 2);
                            if u >= 1 && possible_state(bills@, old_i, u - 1) && remaining_fives(bills@, old_i, u - 1) >= 1 && remaining_tens(bills@, old_i, u - 1) >= 1 {
                                lemma_step_bill_20_use_ten(bills@, old_i, u - 1);
                                assert(remaining_fives(bills@, old_i, u - 1) <= old_five);
                            } else {
                                lemma_step_bill_20_use_fives(bills@, old_i, u);
                                assert(possible_state(bills@, old_i, u));
                                assert(remaining_fives(bills@, old_i, u) <= old_five);
                            }
                        };
                    }
                } else if five >= 3 {
                    five = five - 3;
                    proof {
                        assert(bills@[old_i as int] == 20);
                        lemma_step_bill_20_use_fives(bills@, old_i, old_used_ten);
                        assert(possible_state(bills@, old_i + 1, old_used_ten));
                        assert forall |u: int| (#[trigger] possible_state(bills@, old_i + 1, u)) implies u <= used_ten as int by {
                            reveal_with_fuel(possible_state, 2);
                            if u >= 1 && possible_state(bills@, old_i, u - 1) && remaining_fives(bills@, old_i, u - 1) >= 1 && remaining_tens(bills@, old_i, u - 1) >= 1 {
                                assert(old_ten == remaining_tens(bills@, old_i, old_used_ten));
                                assert(remaining_tens(bills@, old_i, old_used_ten) == 0);
                                assert(remaining_tens(bills@, old_i, u - 1) >= 1);
                                assert(u - 1 < old_used_ten);
                                assert(u <= old_used_ten);
                            } else {
                                assert(possible_state(bills@, old_i, u));
                                assert(u <= old_used_ten);
                            }
                        };
                        assert forall |u: int| (#[trigger] possible_state(bills@, old_i + 1, u)) implies remaining_fives(bills@, old_i + 1, u) <= five as int by {
                            reveal_with_fuel(possible_state, 2);
                            if u >= 1 && possible_state(bills@, old_i, u - 1) && remaining_fives(bills@, old_i, u - 1) >= 1 && remaining_tens(bills@, old_i, u - 1) >= 1 {
                                assert(old_ten == remaining_tens(bills@, old_i, old_used_ten));
                                lemma_tens_positive_implies_fives_smaller(bills@, old_i, u - 1, old_used_ten);
                                lemma_step_bill_20_use_ten(bills@, old_i, u - 1);
                            } else {
                                lemma_step_bill_20_use_fives(bills@, old_i, u);
                                assert(possible_state(bills@, old_i, u));
                                assert(remaining_fives(bills@, old_i, u) <= old_five);
                            }
                        };
                    }
                } else {
                    proof {
                        assert(bills@[old_i as int] == 20);
                        assert forall |u: int| !(#[trigger] possible_state(bills@, old_i + 1, u)) by {
                            reveal_with_fuel(possible_state, 2);
                            if possible_state(bills@, old_i + 1, u) {
                                if u >= 1 && possible_state(bills@, old_i, u - 1) && remaining_fives(bills@, old_i, u - 1) >= 1 && remaining_tens(bills@, old_i, u - 1) >= 1 {
                                    if old_five == 0 {
                                        assert(remaining_fives(bills@, old_i, u - 1) <= old_five);
                                    } else {
                                        assert(old_ten == remaining_tens(bills@, old_i, old_used_ten));
                                        assert(remaining_tens(bills@, old_i, old_used_ten) == 0);
                                        lemma_tens_positive_implies_fives_smaller(bills@, old_i, u - 1, old_used_ten);
                                    }
                                } else {
                                    assert(possible_state(bills@, old_i, u));
                                    assert(remaining_fives(bills@, old_i, u) >= 3);
                                    assert(remaining_fives(bills@, old_i, u) <= old_five);
                                }
                            }
                        };
                        assert(!prefix_possible(bills@, old_i + 1));
                        assert(!can_make_change(bills@)) by {
                            if can_make_change(bills@) {
                                lemma_prefix_possible_of_longer_prefix(bills@, old_i + 1, bills.len() as nat);
                            }
                        };
                    }
                    return false;
                }
            }
            i = i + 1;
        }
        proof {
            assert(can_make_change(bills@)) by {
                assert(possible_state(bills@, bills.len() as nat, used_ten as int));
            }
        }
        true
    }
}

}
