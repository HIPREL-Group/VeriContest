use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn lex_ordered_pair(x: (i64, i64), y: (i64, i64)) -> bool {
    x.0 < y.0 || (x.0 == y.0 && x.1 <= y.1)
}

pub open spec fn ordered_exams(exams: Seq<(i64, i64)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < exams.len() ==> #[trigger] lex_ordered_pair(exams[i], exams[j])
}

pub open spec fn valid_choice(exam: (i64, i64), day: int) -> bool {
    day == exam.0 as int || day == exam.1 as int
}

pub open spec fn ordered_day_pair(days: Seq<int>, i: int, j: int) -> bool
    recommends
        0 <= i <= j < days.len(),
{
    days[i] <= days[j]
}

pub open spec fn feasible_prefix(exams: Seq<(i64, i64)>, prefix_len: int, final_day: int) -> bool
    recommends
        1 <= prefix_len <= exams.len(),
{
    exists|days: Seq<int>|
        days.len() == prefix_len
        && days[prefix_len - 1] == final_day
        && (forall|i: int| 0 <= i < prefix_len ==> #[trigger] valid_choice(exams[i], days[i]))
        && (forall|i: int, j: int| 0 <= i <= j < prefix_len ==> #[trigger] ordered_day_pair(days, i, j))
}

proof fn lemma_valid_choice_upper(exam: (i64, i64), day: int)
    requires
        1 <= exam.1 < exam.0 <= 1_000_000_000,
        valid_choice(exam, day),
    ensures
        day <= exam.0 as int,
{
    if day == exam.1 as int {
        assert(day < exam.0 as int);
    }
}

proof fn lemma_valid_choice_lower(exam: (i64, i64), day: int)
    requires
        1 <= exam.1 < exam.0 <= 1_000_000_000,
        valid_choice(exam, day),
    ensures
        exam.1 as int <= day,
{
    if day == exam.0 as int {
        assert((exam.1 as int) < day);
    }
}

proof fn lemma_feasible_prefix_extend(exams: Seq<(i64, i64)>, prefix_len: int, last: int, next_day: int)
    requires
        1 <= prefix_len < exams.len(),
        feasible_prefix(exams, prefix_len, last),
        last <= next_day,
        valid_choice(exams[prefix_len], next_day),
    ensures
        feasible_prefix(exams, prefix_len + 1, next_day),
{
    let days = choose|days: Seq<int>|
        days.len() == prefix_len
            && days[prefix_len - 1] == last
            && (forall|i: int| 0 <= i < prefix_len ==> valid_choice(exams[i], days[i]))
            && (forall|i: int, j: int| 0 <= i <= j < prefix_len ==> ordered_day_pair(days, i, j));
    let new_days = days.push(next_day);
    assert(new_days.len() == prefix_len + 1);
    assert(new_days[prefix_len] == next_day);
    assert forall|i: int| 0 <= i < prefix_len + 1 implies #[trigger] valid_choice(exams[i], new_days[i]) by {
        if 0 <= i < prefix_len + 1 {
            if i < prefix_len {
                assert(new_days[i] == days[i]);
            } else {
                assert(i == prefix_len);
                assert(new_days[i] == next_day);
            }
        }
    }
    assert forall|i: int, j: int| 0 <= i <= j < prefix_len + 1 implies #[trigger] ordered_day_pair(new_days, i, j) by {
        if 0 <= i <= j < prefix_len + 1 {
            if j < prefix_len {
                assert(new_days[i] == days[i]);
                assert(new_days[j] == days[j]);
                assert(ordered_day_pair(days, i, j));
            } else {
                assert(j == prefix_len);
                if i < prefix_len {
                    assert(new_days[i] == days[i]);
                    assert(ordered_day_pair(days, i, prefix_len - 1));
                    assert(days[prefix_len - 1] == last);
                    assert(new_days[j] == next_day);
                } else {
                    assert(i == prefix_len);
                    assert(new_days[i] == next_day);
                    assert(new_days[j] == next_day);
                }
            }
        }
    }
}

proof fn lemma_feasible_prefix_pop(exams: Seq<(i64, i64)>, prefix_len: int, final_day: int)
    requires
        2 <= prefix_len <= exams.len(),
        feasible_prefix(exams, prefix_len, final_day),
    ensures
        exists|prev: int| #[trigger] feasible_prefix(exams, prefix_len - 1, prev) && prev <= final_day,
{
    let days = choose|days: Seq<int>|
        days.len() == prefix_len
            && days[prefix_len - 1] == final_day
            && (forall|i: int| 0 <= i < prefix_len ==> valid_choice(exams[i], days[i]))
            && (forall|i: int, j: int| 0 <= i <= j < prefix_len ==> ordered_day_pair(days, i, j));
    let prev = days[prefix_len - 2];
    let prefix_days = days.subrange(0, prefix_len - 1);
    assert(prefix_days.len() == prefix_len - 1);
    assert(prefix_days[prefix_len - 2] == prev);
    assert(prev <= final_day) by {
        assert(ordered_day_pair(days, prefix_len - 2, prefix_len - 1));
    }
    assert forall|i: int| 0 <= i < prefix_len - 1 implies #[trigger] valid_choice(exams[i], prefix_days[i]) by {
        if 0 <= i < prefix_len - 1 {
            assert(prefix_days[i] == days[i]);
        }
    }
    assert forall|i: int, j: int| 0 <= i <= j < prefix_len - 1 implies #[trigger] ordered_day_pair(prefix_days, i, j) by {
        if 0 <= i <= j < prefix_len - 1 {
            assert(prefix_days[i] == days[i]);
            assert(prefix_days[j] == days[j]);
            assert(ordered_day_pair(days, i, j));
        }
    }
    assert(feasible_prefix(exams, prefix_len - 1, prev));
}

proof fn lemma_feasible_prefix_last_upper(exams: Seq<(i64, i64)>, prefix_len: int, final_day: int)
    requires
        1 <= prefix_len <= exams.len(),
        forall|i: int| 0 <= i < exams.len() ==> 1 <= #[trigger] exams[i].1 < exams[i].0 <= 1_000_000_000,
        feasible_prefix(exams, prefix_len, final_day),
    ensures
        final_day <= exams[prefix_len - 1].0 as int,
{
    let days = choose|days: Seq<int>|
        days.len() == prefix_len
            && days[prefix_len - 1] == final_day
            && (forall|i: int| 0 <= i < prefix_len ==> valid_choice(exams[i], days[i]))
            && (forall|i: int, j: int| 0 <= i <= j < prefix_len ==> ordered_day_pair(days, i, j));
    assert(valid_choice(exams[prefix_len - 1], days[prefix_len - 1]));
    lemma_valid_choice_upper(exams[prefix_len - 1], days[prefix_len - 1]);
}

proof fn lemma_feasible_prefix_next_upper(exams: Seq<(i64, i64)>, prefix_len: int, final_day: int)
    requires
        1 <= prefix_len < exams.len(),
        ordered_exams(exams),
        forall|i: int| 0 <= i < exams.len() ==> 1 <= #[trigger] exams[i].1 < exams[i].0 <= 1_000_000_000,
        feasible_prefix(exams, prefix_len, final_day),
    ensures
        final_day <= exams[prefix_len].0 as int,
{
    lemma_feasible_prefix_last_upper(exams, prefix_len, final_day);
    assert(#[trigger] lex_ordered_pair(exams[prefix_len - 1], exams[prefix_len]));
    if exams[prefix_len - 1].0 < exams[prefix_len].0 {
    } else {
        assert(exams[prefix_len - 1].0 == exams[prefix_len].0);
    }
}

impl Solution {
    pub fn min_last_exam_day(exams: Vec<(i64, i64)>) -> (result: i64)
        requires
            1 <= exams.len() <= 5000,
            ordered_exams(exams@),
            forall|i: int|
                0 <= i < exams.len() ==> 1 <= #[trigger] exams[i].1 < exams[i].0 <= 1_000_000_000,
        ensures
            feasible_prefix(exams@, exams.len() as int, result as int),
            forall|day: int|
                #[trigger] feasible_prefix(exams@, exams.len() as int, day) ==> result as int <= day,
    {
        let mut last_day = exams[0].1;
        proof {
            let days = seq![last_day as int];
            assert(days.len() == 1);
            assert(days[0] == last_day as int);
            assert(valid_choice(exams@[0], days[0]));
            assert forall|i: int| 0 <= i < 1 implies #[trigger] valid_choice(exams@[i], days[i]) by {
            }
            assert forall|i: int, j: int| 0 <= i <= j < 1 implies #[trigger] ordered_day_pair(days, i, j) by {
                assert(i == 0);
                assert(j == 0);
            }
            assert(feasible_prefix(exams@, 1, last_day as int));
            assert forall|day: int| #[trigger] feasible_prefix(exams@, 1, day) implies (last_day as int) <= day by {
                let witness = choose|days: Seq<int>|
                    days.len() == 1
                        && days[0] == day
                        && (forall|i: int| 0 <= i < 1 ==> valid_choice(exams@[i], days[i]))
                        && (forall|i: int, j: int| 0 <= i <= j < 1 ==> ordered_day_pair(days, i, j));
                assert(valid_choice(exams@[0], witness[0]));
                lemma_valid_choice_lower(exams@[0], witness[0]);
            }
        }
        let mut i = 1usize;
        proof {
            if i < exams.len() {
                lemma_feasible_prefix_next_upper(exams@, 1, last_day as int);
            }
        }
        while i < exams.len()
            invariant
                1 <= exams.len() <= 5000,
                ordered_exams(exams@),
                forall|k: int| 0 <= k < exams.len() ==> 1 <= #[trigger] exams[k].1 < exams[k].0 <= 1_000_000_000,
                1 <= i <= exams.len(),
                feasible_prefix(exams@, i as int, last_day as int),
                forall|day: int| #[trigger] feasible_prefix(exams@, i as int, day) ==> (last_day as int) <= day,
                i < exams.len() ==> (last_day as int) <= (exams[i as int].0 as int),
            decreases exams.len() - i,
        {
            let a = exams[i].0;
            let b = exams[i].1;
            if b >= last_day {
                proof {
                    lemma_feasible_prefix_extend(exams@, i as int, last_day as int, b as int);
                    assert forall|day: int| #[trigger] feasible_prefix(exams@, i as int + 1, day) implies (b as int) <= day by {
                        let witness = choose|days: Seq<int>|
                            days.len() == i as int + 1
                                && days[i as int] == day
                                && (forall|k: int| 0 <= k < i as int + 1 ==> valid_choice(exams@[k], days[k]))
                                && (forall|p: int, q: int| 0 <= p <= q < i as int + 1 ==> ordered_day_pair(days, p, q));
                        assert(valid_choice(exams@[i as int], witness[i as int]));
                        lemma_valid_choice_lower(exams@[i as int], witness[i as int]);
                    }
                    if i + 1 < exams.len() {
                        lemma_feasible_prefix_next_upper(exams@, i as int + 1, b as int);
                    }
                }
                last_day = b;
            } else {
                proof {
                    lemma_feasible_prefix_extend(exams@, i as int, last_day as int, a as int);
                    assert forall|day: int| #[trigger] feasible_prefix(exams@, i as int + 1, day) implies (a as int) <= day by {
                        let witness = choose|days: Seq<int>|
                            days.len() == i as int + 1
                                && days[i as int] == day
                                && (forall|k: int| 0 <= k < i as int + 1 ==> valid_choice(exams@[k], days[k]))
                                && (forall|p: int, q: int| 0 <= p <= q < i as int + 1 ==> ordered_day_pair(days, p, q));
                        assert(valid_choice(exams@[i as int], witness[i as int]));
                        if witness[i as int] == b as int {
                            lemma_feasible_prefix_pop(exams@, i as int + 1, day);
                            let prev = choose|prev: int| feasible_prefix(exams@, i as int, prev) && prev <= day;
                            assert((last_day as int) <= prev);
                            assert(prev <= day);
                            assert((b as int) < (last_day as int));
                            assert(false);
                        } else {
                            assert(witness[i as int] == a as int);
                        }
                    }
                    if i + 1 < exams.len() {
                        lemma_feasible_prefix_next_upper(exams@, i as int + 1, a as int);
                    }
                }
                last_day = a;
            }
            i += 1;
        }
        last_day
    }
}

}
