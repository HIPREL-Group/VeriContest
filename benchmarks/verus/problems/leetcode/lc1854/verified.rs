use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn population(logs: Seq<Vec<i32>>, year: int, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::population(logs, year, n - 1)
                + if logs[n - 1][0] as int <= year && year < logs[n - 1][1] as int {
                    1int
                } else {
                    0int
                }
        }
    }

    pub fn maximum_population(logs: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= logs.len() <= 100,
            forall|i: int|
                0 <= i < logs.len() ==> (#[trigger] logs[i].len() == 2 && 1950 <= logs[i][0]
                    && logs[i][0] < logs[i][1] && logs[i][1] <= 2050),
        ensures
            1950 <= result <= 2049,
            forall|y: int|
                1950 <= y <= 2049 ==> Self::population(logs@, result as int, logs@.len() as int)
                    >= #[trigger] Self::population(logs@, y, logs@.len() as int),
            forall|y: int|
                1950 <= y < result ==> Self::population(logs@, result as int, logs@.len() as int)
                    > #[trigger] Self::population(logs@, y, logs@.len() as int),
    {
        let n = logs.len();
        let mut best_year: i32 = 1950;
        let mut max_pop: i32 = 0;
        let mut year: i32 = 1950;

        while year <= 2049
            invariant
                1950 <= year <= 2050,
                1950 <= best_year <= 2049,
                0 <= max_pop <= 100,
                n == logs.len(),
                1 <= n <= 100,
                forall|j: int|
                    0 <= j < n ==> (#[trigger] logs[j].len() == 2 && 1950 <= logs[j][0]
                        && logs[j][0] < logs[j][1] && logs[j][1] <= 2050),
                best_year < year || year == 1950,
                year > 1950 ==> max_pop as int == Self::population(
                    logs@,
                    best_year as int,
                    n as int,
                ),
                year == 1950 ==> max_pop == 0 && best_year == 1950,
                forall|y: int|
                    1950 <= y < year as int ==> Self::population(logs@, y, n as int)
                        <= max_pop as int,
                forall|y: int|
                    1950 <= y < best_year as int ==> Self::population(logs@, y, n as int)
                        < max_pop as int,
            decreases 2050 - year,
        {
            let mut pop: i32 = 0;
            let mut i: usize = 0;

            while i < n
                invariant
                    0 <= i <= n,
                    n == logs.len(),
                    1 <= n <= 100,
                    0 <= pop as int <= i as int,
                    1950 <= year <= 2049,
                    forall|j: int|
                        0 <= j < n ==> (#[trigger] logs[j].len() == 2 && 1950 <= logs[j][0]
                            && logs[j][0] < logs[j][1] && logs[j][1] <= 2050),
                    pop as int == Self::population(logs@, year as int, i as int),
                decreases n - i,
            {
                assert(logs[i as int].len() == 2);
                if logs[i][0] <= year && year < logs[i][1] {
                    pop += 1;
                }
                i += 1;
            }

            if pop > max_pop {
                max_pop = pop;
                best_year = year;
            }
            year += 1;
        }
        best_year
    }
}

}
