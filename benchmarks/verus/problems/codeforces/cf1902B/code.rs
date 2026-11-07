impl Solution {
    pub fn max_rest_days(n: i64, p: i64, l: i64, t: i64) -> i64 {
        let tasks: i64 = (n + 6) / 7;
        let pairs: i64 = tasks / 2;
        let odd: i64 = tasks % 2;
        let pair_pts: i64 = l + 2 * t;

        let pair_total: i64 = pairs * pair_pts;
        let mut study_days: i64;

        if p <= pair_total {
            if p % pair_pts == 0 {
                study_days = p / pair_pts;
            } else {
                study_days = p / pair_pts + 1;
            }
        } else {
            study_days = pairs;
            let mut rem: i64 = if p >= pair_total { p - pair_total } else { 0 };
            if odd == 1 {
                let one_day_pts: i64 = l + t;
                if rem <= one_day_pts {
                    study_days = study_days + 1;
                    rem = 0;
                } else {
                    study_days = study_days + 1;
                    rem = rem - one_day_pts;
                }
            }
            if rem > 0 {
                if rem % l == 0 {
                    study_days = study_days + rem / l;
                } else {
                    study_days = study_days + rem / l + 1;
                }
            }
        }

        n - study_days
    }
}
