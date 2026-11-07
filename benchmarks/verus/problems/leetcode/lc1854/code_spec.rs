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
        while year <= 2049 {
            let mut pop: i32 = 0;
            let mut i: usize = 0;
            while i < n {
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
