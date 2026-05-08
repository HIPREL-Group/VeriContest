use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_prefix(s: Seq<i32>, p: int, len: int) -> int
        recommends
            0 <= len <= s.len(),
        decreases len,
    {
        if len <= 0 {
            0
        } else {
            Self::count_prefix(s, p, len - 1) + if s[len - 1] == p as i32 { 1int } else { 0int }
        }
    }

    pub proof fn lemma_count_prefix_bounds(s: Seq<i32>, p: int, len: int)
        requires
            0 <= len <= s.len(),
        ensures
            0 <= Self::count_prefix(s, p, len) <= len,
        decreases len,
    {
        if len <= 0 {
        } else {
            Self::lemma_count_prefix_bounds(s, p, len - 1);
            assert(0 <= Self::count_prefix(s, p, len - 1) <= len - 1);
            assert(Self::count_prefix(s, p, len)
                == Self::count_prefix(s, p, len - 1) + if s[len - 1] == p as i32 { 1int } else { 0int });
            if s[len - 1] == p as i32 {
                assert(Self::count_prefix(s, p, len) <= len);
            } else {
                assert(Self::count_prefix(s, p, len) <= len);
            }
        }
    }

    pub open spec fn count_value(s: Seq<i32>, p: int) -> int {
        Self::count_prefix(s, p, s.len() as int)
    }

    pub open spec fn abs_int(x: int) -> int {
        if x >= 0 { x } else { -x }
    }

    pub open spec fn moves_from(pos: int, balance: int, seats: Seq<i32>, students: Seq<i32>) -> int
        decreases if pos <= 100 { 101 - pos } else { 0int },
    {
        if pos > 100 {
            0
        } else {
            let next_balance = balance + Self::count_value(seats, pos) - Self::count_value(students, pos);
            Self::abs_int(next_balance) + Self::moves_from(pos + 1, next_balance, seats, students)
        }
    }

    pub fn min_moves_to_seat(seats: Vec<i32>, students: Vec<i32>) -> (result: i32)
        requires
            1 <= seats.len() <= 100,
            students.len() == seats.len(),
            seats@.len() <= 100,
            students@.len() == seats@.len(),
            forall |i: int| 0 <= i < seats.len() ==> 1 <= #[trigger] seats[i] <= 100,
            forall |i: int| 0 <= i < students.len() ==> 1 <= #[trigger] students[i] <= 100,
        ensures
            result as int == Self::moves_from(1, 0, seats@, students@),
    {
        let mut answer: i32 = 0;
        let mut balance: i32 = 0;
        let mut pos: i32 = 1;

        while pos <= 100
            invariant
                1 <= pos <= 101,
                seats@.len() <= 100,
                students@.len() == seats@.len(),
                -100 * (pos - 1) <= balance <= 100 * (pos - 1),
                0 <= answer,
                2 * answer <= 100 * (pos - 1) * pos,
                answer as int + Self::moves_from(pos as int, balance as int, seats@, students@)
                    == Self::moves_from(1, 0, seats@, students@),
            decreases 101 - pos,
        {
            let ghost old_balance = balance;
            let ghost old_answer = answer;
            let ghost old_pos = pos;

            let mut seat_cnt: i32 = 0;
            let mut i: usize = 0;
            while i < seats.len()
                invariant
                    0 <= i <= seats.len(),
                    seats@.len() <= 100,
                    0 <= seat_cnt,
                    seat_cnt as int == Self::count_prefix(seats@, pos as int, i as int),
                decreases seats.len() - i,
            {
                if seats[i] == pos {
                    proof {
                        Self::lemma_count_prefix_bounds(seats@, pos as int, i as int);
                        assert((seat_cnt as int) == Self::count_prefix(seats@, pos as int, i as int));
                        assert((seat_cnt as int) <= (i as int));
                        assert((i as int) < seats@.len());
                        assert((seats@.len()) <= 100);
                        assert((seat_cnt as int) < 100);
                        assert(seat_cnt < 2_147_483_647);
                    }
                    seat_cnt = seat_cnt + 1;
                }
                i = i + 1;
            }

            let mut student_cnt: i32 = 0;
            let mut j: usize = 0;
            while j < students.len()
                invariant
                    0 <= j <= students.len(),
                    students@.len() <= 100,
                    0 <= student_cnt,
                    student_cnt as int == Self::count_prefix(students@, pos as int, j as int),
                decreases students.len() - j,
            {
                if students[j] == pos {
                    proof {
                        Self::lemma_count_prefix_bounds(students@, pos as int, j as int);
                        assert((student_cnt as int) == Self::count_prefix(students@, pos as int, j as int));
                        assert((student_cnt as int) <= (j as int));
                        assert((j as int) < students@.len());
                        assert((students@.len()) <= 100);
                        assert((student_cnt as int) < 100);
                        assert(student_cnt < 2_147_483_647);
                    }
                    student_cnt = student_cnt + 1;
                }
                j = j + 1;
            }

            proof {
                assert(i == seats.len());
                assert(j == students.len());
                Self::lemma_count_prefix_bounds(seats@, pos as int, i as int);
                Self::lemma_count_prefix_bounds(students@, pos as int, j as int);
                assert((seat_cnt as int) == Self::count_value(seats@, pos as int));
                assert((student_cnt as int) == Self::count_value(students@, pos as int));
                assert(0 <= (seat_cnt as int) <= seats@.len());
                assert(0 <= (student_cnt as int) <= students@.len());
                assert((seat_cnt as int) <= 100);
                assert((student_cnt as int) <= 100);
                assert(-100 * (old_pos - 1) <= old_balance <= 100 * (old_pos - 1));
                assert(-100 <= seat_cnt - student_cnt <= 100);
                assert(-100 * old_pos <= old_balance + seat_cnt - student_cnt <= 100 * old_pos);
                assert(-2_147_483_648 <= balance + seat_cnt - student_cnt < 2_147_483_647);
            }

            let next_balance: i32 = balance + seat_cnt - student_cnt;
            balance = next_balance;

            if balance >= 0 {
                proof {
                    assert(old_pos <= 100);
                    assert(balance <= 100 * old_pos);
                    assert(0 <= old_answer);
                    assert(2 * old_answer <= 100 * (old_pos - 1) * old_pos);
                    assert(2 * (old_answer + balance) == 2 * old_answer + 2 * balance);
                    assert(2 * balance <= 200 * old_pos);
                    assert(2 * (old_answer + balance) <= 100 * old_pos * (old_pos + 1)) by (nonlinear_arith)
                        requires
                            2 * old_answer <= 100 * (old_pos - 1) * old_pos,
                            2 * balance <= 200 * old_pos,
                            old_pos >= 0;
                    assert(old_pos <= 100);
                    assert(old_pos >= 1);
                    assert(100 * old_pos * (old_pos + 1) <= 2_000_000) by (nonlinear_arith)
                        requires
                            old_pos >= 1,
                            old_pos <= 100;
                    assert(2 * (old_answer + balance) <= 2_000_000) by (nonlinear_arith)
                        requires
                            2 * (old_answer + balance) <= 100 * old_pos * (old_pos + 1),
                            100 * old_pos * (old_pos + 1) <= 2_000_000;
                    assert(0 <= old_answer + balance);
                    assert(old_answer + balance <= 1_000_000) by (nonlinear_arith)
                        requires
                            0 <= old_answer + balance,
                            2 * (old_answer + balance) <= 2_000_000;
                    assert(answer == old_answer);
                    assert(answer + balance <= 1_000_000);
                    assert(answer + balance < 2_147_483_647);
                    assert(-2_147_483_648 <= answer + balance < 2_147_483_647);
                    assert(balance as int == Self::abs_int(balance as int));
                }
                answer = answer + balance;
                proof {
                    assert(answer == old_answer + balance);
                }
            } else {
                proof {
                    assert(old_pos <= 100);
                    assert(balance >= -100 * old_pos);
                    assert(-balance <= 100 * old_pos);
                    assert(0 <= old_answer);
                    assert(2 * old_answer <= 100 * (old_pos - 1) * old_pos);
                    assert(2 * (old_answer - balance) == 2 * old_answer + 2 * (-balance));
                    assert(2 * (-balance) <= 200 * old_pos);
                    assert(2 * (old_answer - balance) <= 100 * old_pos * (old_pos + 1)) by (nonlinear_arith)
                        requires
                            2 * old_answer <= 100 * (old_pos - 1) * old_pos,
                            2 * (-balance) <= 200 * old_pos,
                            old_pos >= 0;
                    assert(old_pos <= 100);
                    assert(old_pos >= 1);
                    assert(100 * old_pos * (old_pos + 1) <= 2_000_000) by (nonlinear_arith)
                        requires
                            old_pos >= 1,
                            old_pos <= 100;
                    assert(2 * (old_answer - balance) <= 2_000_000) by (nonlinear_arith)
                        requires
                            2 * (old_answer - balance) <= 100 * old_pos * (old_pos + 1),
                            100 * old_pos * (old_pos + 1) <= 2_000_000;
                    assert(0 <= old_answer - balance);
                    assert(old_answer - balance <= 1_000_000) by (nonlinear_arith)
                        requires
                            0 <= old_answer - balance,
                            2 * (old_answer - balance) <= 2_000_000;
                    assert(answer == old_answer);
                    assert(answer - balance <= 1_000_000);
                    assert(answer - balance < 2_147_483_647);
                    assert(-2_147_483_648 <= answer - balance < 2_147_483_647);
                    assert((-balance) as int == Self::abs_int(balance as int));
                }
                answer = answer - balance;
                proof {
                    assert(answer == old_answer - balance);
                }
            }

            proof {
                assert((next_balance as int)
                    == (old_balance as int)
                        + Self::count_value(seats@, old_pos as int)
                        - Self::count_value(students@, old_pos as int));
                assert(Self::moves_from(old_pos as int, old_balance as int, seats@, students@)
                    == Self::abs_int(next_balance as int)
                        + Self::moves_from(old_pos as int + 1, next_balance as int, seats@, students@));
                assert((answer as int) == (old_answer as int) + Self::abs_int(next_balance as int));
                assert(answer as int + Self::moves_from((old_pos + 1) as int, next_balance as int, seats@, students@)
                    == Self::moves_from(1, 0, seats@, students@));
                assert(-100 * old_pos <= balance <= 100 * old_pos);
                assert(0 <= answer);
                assert(2 * answer <= 100 * old_pos * (old_pos + 1));
            }

            pos = pos + 1;
        }

        answer
    }
}

}
