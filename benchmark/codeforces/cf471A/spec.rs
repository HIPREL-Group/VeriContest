use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn count_eq_prefix(a: Seq<i32>, i: int, v: i32) -> int
    decreases i,
{
    if i <= 0 {
        0
    } else {
        count_eq_prefix(a, i - 1, v) + (if a[i - 1] == v { 1int } else { 0int })
    }
}

pub open spec fn leg_scan_upto_v(a: Seq<i32>, upto: int) -> int
    recommends 0 <= upto <= 9,
{
    let r1 = if count_eq_prefix(a, 6, 1) >= 4 { 1int } else { 0int };
    let r2 = if count_eq_prefix(a, 6, 2) >= 4 { 2 } else { r1 };
    let r3 = if count_eq_prefix(a, 6, 3) >= 4 { 3 } else { r2 };
    let r4 = if count_eq_prefix(a, 6, 4) >= 4 { 4 } else { r3 };
    let r5 = if count_eq_prefix(a, 6, 5) >= 4 { 5 } else { r4 };
    let r6 = if count_eq_prefix(a, 6, 6) >= 4 { 6 } else { r5 };
    let r7 = if count_eq_prefix(a, 6, 7) >= 4 { 7 } else { r6 };
    let r8 = if count_eq_prefix(a, 6, 8) >= 4 { 8 } else { r7 };
    let r9 = if count_eq_prefix(a, 6, 9) >= 4 { 9 } else { r8 };
    if upto == 0 {
        0
    } else if upto == 1 {
        r1
    } else if upto == 2 {
        r2
    } else if upto == 3 {
        r3
    } else if upto == 4 {
        r4
    } else if upto == 5 {
        r5
    } else if upto == 6 {
        r6
    } else if upto == 7 {
        r7
    } else if upto == 8 {
        r8
    } else {
        r9
    }
}

pub open spec fn leg_length_if_any(a: Seq<i32>) -> int {
    leg_scan_upto_v(a, 9)
}

pub open spec fn remaining_two_equal(a: Seq<i32>, leg: int) -> bool {
    exists|i: int, j: int|
        0 <= i < j < 6
        && #[trigger] a[i] as int != leg
        && #[trigger] a[j] as int != leg
        && (forall|k: int|
            0 <= k < 6 && k != i && k != j ==> #[trigger] a[k] as int == leg)
        && a[i] == a[j]
}

pub open spec fn classify_with_leg(a: Seq<i32>, leg: int) -> int
    recommends
        1 <= leg <= 9,
{
    let c = count_eq_prefix(a, 6, leg as i32);
    if c == 6 {
        2
    } else if c == 5 {
        1
    } else {
        if remaining_two_equal(a, leg) {
            2
        } else {
            1
        }
    }
}

pub open spec fn expected_animal(a: Seq<i32>) -> int {
    let leg = leg_length_if_any(a);
    if leg == 0 {
        0
    } else {
        classify_with_leg(a, leg)
    }
}

pub struct Solution;

impl Solution {
    pub fn animal_type(sticks: Vec<i32>) -> (res: i32)
        requires
            sticks.len() == 6,
            forall|i: int| 0 <= i < 6 ==> 1 <= #[trigger] sticks@[i] as int <= 9,
        ensures
            res == expected_animal(sticks@),
    {
    }
}

}
