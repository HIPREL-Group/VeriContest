use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn row_of_x(x: int, n: int) -> int {
    (x - 1) % n + 1
}

pub open spec fn col_of_x(x: int, n: int) -> int {
    (x - 1) / n + 1
}

impl Solution {
    pub fn strange_table_number(n: u64, m: u64, x: u64) -> (result: u64)
        requires
            1 <= n <= 1_000_000,
            1 <= m <= 1_000_000,
            1 <= x <= n * m,
        ensures
            result as int == (row_of_x(x as int, n as int) - 1) * m as int + col_of_x(x as int, n as int),
    {
        let row = (x - 1) % n + 1;
        let col = (x - 1) / n + 1;

        proof {
            assert(1 <= row <= n);
            assert(1 <= col);
            assert((x as int - 1) / n as int <= m as int - 1) by (nonlinear_arith)
                requires
                    1 <= x,
                    x <= n * m,
                    1 <= n,
            {
            }
            assert(col as int <= m as int);
            assert((((row - 1) as int) * (m as int) + (col as int)) <= n as int * m as int) by (nonlinear_arith)
                requires
                    1 <= row <= n,
                    1 <= m,
                    1 <= col,
                    col <= m,
            {
            }
            assert(n as int * m as int <= 1_000_000_000_000) by (nonlinear_arith)
                requires
                    n <= 1_000_000,
                    m <= 1_000_000,
            {
            }
            assert((((row - 1) as int) * (m as int) + (col as int)) <= 1_000_000_000_000);
            assert(1_000_000_000_000 < u128::MAX as int) by (nonlinear_arith) {
            }
        }

        let ans = ((row - 1) as u128) * (m as u128) + (col as u128);

        proof {
            assert(row as int == row_of_x(x as int, n as int));
            assert(col as int == col_of_x(x as int, n as int));
            assert(0 <= ((row - 1) as int) * (m as int) + (col as int));
            assert(1_000_000_000_000 < u64::MAX as int) by (nonlinear_arith) {
            }
            assert(ans as int == ((row - 1) as int) * (m as int) + (col as int));
        }

        ans as u64
    }
}

}
