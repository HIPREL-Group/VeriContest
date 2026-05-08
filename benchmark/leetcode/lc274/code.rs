impl Solution {
    pub fn h_index(citations: Vec<i32>) -> i32
    {
        let n = citations.len();

        let mut h: usize = n;
        while h > 0 
        {
            let mut count: usize = 0;
            let mut j: usize = 0;
            
            while j < n 
            {
                if citations[j] >= h as i32 {
                    count = count + 1;
                } 
                
                j = j + 1;
            }
            
            if count >= h 
            {
                return h as i32;
            }
            
            h = h - 1;
        }

        0
    }
}
