impl Solution {
    pub fn h_index(citations: Vec<i32>) -> i32
    {
        let num = citations.len() as i32;
        let mut i: i32 = 0;
        let mut j: i32 = num;

        while i < j 
        {
            let mid = (i + j) / 2;
            if citations[mid as usize] >= (num - mid) {
                j = mid;
            } else {
                i = mid + 1;
            }
        }

        num - i
    }
}
