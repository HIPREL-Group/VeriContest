impl Solution {
    pub fn min_moves_to_seat(seats: Vec<i32>, students: Vec<i32>) -> i32 {
        let mut answer: i32 = 0;
        let mut balance: i32 = 0;
        let mut pos: i32 = 1;

        while pos <= 100 {
            let mut seat_cnt: i32 = 0;
            let mut i: usize = 0;
            while i < seats.len() {
                if seats[i] == pos {
                    seat_cnt = seat_cnt + 1;
                }
                i = i + 1;
            }

            let mut student_cnt: i32 = 0;
            let mut j: usize = 0;
            while j < students.len() {
                if students[j] == pos {
                    student_cnt = student_cnt + 1;
                }
                j = j + 1;
            }

            let next_balance: i32 = balance + seat_cnt - student_cnt;
            balance = next_balance;

            if balance >= 0 {
                answer = answer + balance;
            } else {
                answer = answer - balance;
            }

            pos = pos + 1;
        }

        answer
    }
}
