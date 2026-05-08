impl Solution {
    pub fn matrix_sum_queries(n: i32, queries: Vec<Vec<i32>>) -> i64 {
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
