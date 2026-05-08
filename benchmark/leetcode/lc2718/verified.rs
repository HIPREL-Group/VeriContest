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
            let ghost total = Self::backward_sum(
                queries@,
                n as int,
                queries@.len() as int,
                Seq::<i32>::empty(),
                Seq::<i32>::empty(),
            );
            
            let mut i: usize = queries.len();
            while i > 0
                invariant
                    i <= queries.len(),
                    n_usize == n as usize,
                    1 <= n <= 10000,
                    n_usize <= 10000,
                    seen_rows.len() <= n_usize,
                    seen_cols.len() <= n_usize,
                    0 <= sum,
                    sum as int <= (seen_rows.len() + seen_cols.len()) as int * 1_000_000_000int,
                    queries.len() <= 50000,
                    forall|k: int| 0 <= k < queries.len() ==> queries[k].len() == 3,
                    forall|k: int|
                        0 <= k < queries.len() ==> (#[trigger] queries[k][0] == 0
                            || queries[k][0] == 1),
                    forall|k: int|
                        0 <= k < queries.len() ==> 0 <= queries[k][1] && queries[k][1] < n,
                    forall|k: int|
                        0 <= k < queries.len() ==> 0 <= queries[k][2] && queries[k][2] <= 100000,
                    sum as int + Self::backward_sum(
                        queries@,
                        n as int,
                        i as int,
                        seen_rows@,
                        seen_cols@,
                    ) == total,
                decreases i
            {
                i = i - 1;
                let ghost old_sr = seen_rows@;
                let ghost old_sc = seen_cols@;
                let ghost old_sum = sum;
                assert(queries[i as int].len() == 3);
                assert(0 <= queries[i as int][2] && queries[i as int][2] <= 100000);
                let query_type = queries[i][0];
                let index = queries[i][1];
                let value = queries[i][2] as i64;
                
                if query_type == 0 {
                    let mut found = false;
                    let mut j: usize = 0;
                    while j < seen_rows.len()
                        invariant
                            0 <= j <= seen_rows.len(),
                            seen_rows.len() <= n_usize,
                            n_usize <= 10000,
                            found ==> (exists|k: int|
                                0 <= k < j as int && seen_rows@[k] == index),
                            !found ==> (forall|k: int|
                                0 <= k < j as int ==> seen_rows@[k] != index),
                        decreases seen_rows.len() - j
                    {
                        if seen_rows[j] == index {
                            assert(seen_rows@[j as int] == index);
                            found = true;
                        }
                        j = j + 1;
                    }
                    assert(found == Self::seq_contains(seen_rows@, index));
                    
                    if !found {
                        if seen_rows.len() < n_usize {
                            let unseen_cols_usize = if seen_cols.len() < n_usize {
                                n_usize - seen_cols.len()
                            } else {
                                0usize
                            };
                            let unseen_cols = unseen_cols_usize as i64;
                            assert(0 <= value && value <= 100000);
                            assert(0 <= unseen_cols && unseen_cols <= 10000);
                            assert(value as int * unseen_cols as int <= 1_000_000_000) by (nonlinear_arith)
                                requires value <= 100000, unseen_cols <= 10000, value >= 0, unseen_cols >= 0;
                            let contrib = value * unseen_cols;
                            assert(sum as int + contrib as int <= 20001 * 1_000_000_000) by (nonlinear_arith)
                                requires
                                    sum as int <= (seen_rows.len() + seen_cols.len()) as int * 1_000_000_000,
                                    seen_rows.len() + seen_cols.len() <= 20000,
                                    0 <= contrib && contrib <= 1_000_000_000,
                                    sum >= 0;
                            sum = sum + contrib;
                            seen_rows.push(index);
                        }
                    }
                } else {
                    let mut found = false;
                    let mut j: usize = 0;
                    while j < seen_cols.len()
                        invariant
                            0 <= j <= seen_cols.len(),
                            seen_cols.len() <= n_usize,
                            n_usize <= 10000,
                            found ==> (exists|k: int|
                                0 <= k < j as int && seen_cols@[k] == index),
                            !found ==> (forall|k: int|
                                0 <= k < j as int ==> seen_cols@[k] != index),
                        decreases seen_cols.len() - j
                    {
                        if seen_cols[j] == index {
                            assert(seen_cols@[j as int] == index);
                            found = true;
                        }
                        j = j + 1;
                    }
                    assert(found == Self::seq_contains(seen_cols@, index));
                    
                    if !found {
                        if seen_cols.len() < n_usize {
                            let unseen_rows_usize = if seen_rows.len() < n_usize {
                                n_usize - seen_rows.len()
                            } else {
                                0usize
                            };
                            let unseen_rows = unseen_rows_usize as i64;
                            assert(0 <= value && value <= 100000);
                            assert(0 <= unseen_rows && unseen_rows <= 10000);
                            assert(value as int * unseen_rows as int <= 1_000_000_000) by (nonlinear_arith)
                                requires value <= 100000, unseen_rows <= 10000, value >= 0, unseen_rows >= 0;
                            let contrib = value * unseen_rows;
                            assert(sum as int + contrib as int <= 20001 * 1_000_000_000) by (nonlinear_arith)
                                requires
                                    sum as int <= (seen_rows.len() + seen_cols.len()) as int * 1_000_000_000,
                                    seen_rows.len() + seen_cols.len() <= 20000,
                                    0 <= contrib && contrib <= 1_000_000_000,
                                    sum >= 0;
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
