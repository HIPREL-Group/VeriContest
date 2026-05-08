use vstd::prelude::*;

fn main() {}

verus! {
    pub struct Solution;

    impl Solution {
        pub open spec fn seq_contains(s: Seq<i32>, x: i32) -> bool {
            exists|i: int| 0 <= i < s.len() && s[i] == x
        }

        pub open spec fn backward_sum(
            queries: Seq<Vec<i32>>,
            n: int,
            k: int,
            seen_rows: Seq<i32>,
            seen_cols: Seq<i32>,
        ) -> int
            decreases k,
        {
            if k <= 0 {
                0int
            } else {
                let j = k - 1;
                let qtype = queries[j][0];
                let index = queries[j][1];
                let value = queries[j][2] as int;
                if qtype == 0 {
                    if Self::seq_contains(seen_rows, index) || seen_rows.len() >= n {
                        Self::backward_sum(queries, n, j, seen_rows, seen_cols)
                    } else {
                        let unseen = if seen_cols.len() < n { n - seen_cols.len() } else { 0int };
                        value * unseen
                            + Self::backward_sum(
                                queries, n, j, seen_rows.push(index), seen_cols,
                            )
                    }
                } else {
                    if Self::seq_contains(seen_cols, index) || seen_cols.len() >= n {
                        Self::backward_sum(queries, n, j, seen_rows, seen_cols)
                    } else {
                        let unseen = if seen_rows.len() < n { n - seen_rows.len() } else { 0int };
                        value * unseen
                            + Self::backward_sum(
                                queries, n, j, seen_rows, seen_cols.push(index),
                            )
                    }
                }
            }
        }

        pub fn matrix_sum_queries(n: i32, queries: Vec<Vec<i32>>) -> (res: i64)
            requires
                1 <= n <= 10000,
                1 <= queries.len() <= 50000,
                forall|i: int| 0 <= i < queries.len() ==> queries[i].len() == 3,
                forall|i: int| 0 <= i < queries.len() ==> (#[trigger] queries[i][0] == 0 || queries[i][0] == 1),
                forall|i: int| 0 <= i < queries.len() ==> 0 <= queries[i][1] && queries[i][1] < n,
                forall|i: int| 0 <= i < queries.len() ==> 0 <= queries[i][2] && queries[i][2] <= 100000,
            ensures
                res as int == Self::backward_sum(
                    queries@,
                    n as int,
                    queries@.len() as int,
                    Seq::<i32>::empty(),
                    Seq::<i32>::empty(),
                ),
        {
            let mut sum = 0i64;
            let mut seen_rows = Vec::new();
            let mut seen_cols = Vec::new();
            let n_usize: usize = n as usize;
            
            let mut i: usize = queries.len();
            while i > 0 {
                i = i - 1;
                let query_type = queries[i][0];
                let index = queries[i][1];
                let value = queries[i][2] as i64;
                
                if query_type == 0 {
                    let mut found = false;
                    let mut j: usize = 0;
                    while j < seen_rows.len() {
                        if seen_rows[j] == index {
                            found = true;
                        }
                        j = j + 1;
                    }
                    
                    if !found {
                        if seen_rows.len() < n_usize {
                            let unseen_cols_usize = if seen_cols.len() < n_usize {
                                n_usize - seen_cols.len()
                            } else {
                                0usize
                            };
                            let unseen_cols = unseen_cols_usize as i64;
                            let contrib = value * unseen_cols;
                            sum = sum + contrib;
                            seen_rows.push(index);
                        }
                    }
                } else {
                    let mut found = false;
                    let mut j: usize = 0;
                    while j < seen_cols.len() {
                        if seen_cols[j] == index {
                            found = true;
                        }
                        j = j + 1;
                    }
                    
                    if !found {
                        if seen_cols.len() < n_usize {
                            let unseen_rows_usize = if seen_rows.len() < n_usize {
                                n_usize - seen_rows.len()
                            } else {
                                0usize
                            };
                            let unseen_rows = unseen_rows_usize as i64;
                            let contrib = value * unseen_rows;
                            sum = sum + contrib;
                            seen_cols.push(index);
                        }
                    }
                }
            }
            
            sum
        }
    }
}
