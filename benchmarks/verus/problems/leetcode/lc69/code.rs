impl Solution {
    pub fn my_sqrt(x: i32) -> i32
    {
        let num: u64 = x as u64;
        let mut i: u64 = 0;
        let mut j: u64 = num;
        let mut found: bool = false; 

        while i <= j && !found
        {
            let mid = (i + j) / 2;
            let tmp = mid * mid;

            if tmp == num {
                found = true;
            } else if tmp > num {
                j = mid - 1;
            } else {
                i = mid + 1;
            }
        }

        ((i + j) / 2) as i32
    }
}
