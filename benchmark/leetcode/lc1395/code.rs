impl Solution {
    pub fn num_teams(rating: Vec<i32>) -> i32 {
        let mut count: i32 = 0;
        let mut i: usize = 0;
        let n: usize = rating.len();
        
        while i < n {
            let mut j: usize = i + 1;
            let mut inner_count_j: i32 = 0;
            
            while j < n {
                let mut k: usize = j + 1;
                let mut inner_count_k: i32 = 0;
                
                while k < n {
                    let ri = rating[i];
                    let rj = rating[j];
                    let rk = rating[k];
                    
                    if (ri < rj && rj < rk) || (ri > rj && rj > rk) {
                        inner_count_k += 1;
                    }
                    k += 1;
                }
                inner_count_j += inner_count_k;
                j += 1;
            }
            count += inner_count_j;
            i += 1;
        }
        
        count
    }
}
