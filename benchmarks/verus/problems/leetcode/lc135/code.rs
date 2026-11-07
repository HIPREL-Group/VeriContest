impl Solution {
    pub fn candy(ratings: Vec<i32>) -> i32 {
        let n = ratings.len();

        
        let mut left: Vec<i32> = Vec::new();
        left.push(1i32);
        let mut i: usize = 1;
        while i < n {
            if ratings[i] > ratings[i - 1] {
                let v = left[i - 1] + 1;
                left.push(v);
            } else {
                left.push(1i32);
            }
            i += 1;
        }

        
        let mut right: Vec<i32> = Vec::new();
        i = 0;
        while i < n {
            right.push(1i32);
            i += 1;
        }

        if n >= 2 {
            let mut idx: usize = n - 1;
            while idx > 0 {
                idx -= 1;
                if ratings[idx] > ratings[idx + 1] {
                    let v = right[idx + 1] + 1;
                    right[idx] = v;
                }
            }
        }

        
        let mut candy: Vec<i32> = Vec::new();
        i = 0;
        while i < n {
            let c = if left[i] > right[i] { left[i] } else { right[i] };
            candy.push(c);
            i += 1;
        }

        
        let mut total: i32 = 0;
        i = 0;
        while i < n {
            total += candy[i];
            i += 1;
        }

        total
    }
}
