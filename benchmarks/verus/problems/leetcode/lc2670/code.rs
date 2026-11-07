impl Solution {
    fn count_distinct(nums: &Vec<i32>, left: usize, right: usize) -> i32 {
        let mut v: i32 = 1;
        let mut count: i32 = 0;
        while v <= 50 {
            let mut j: usize = left;
            let mut found: bool = false;
            while j < right {
                if nums[j] == v {
                    found = true;
                }
                j = j + 1;
            }
            if found {
                count = count + 1;
            }
            v = v + 1;
        }
        count
    }

    pub fn distinct_difference_array(nums: Vec<i32>) -> Vec<i32> {
        let n = nums.len();
        let mut out: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let p = Self::count_distinct(&nums, 0, i + 1);
            let s = Self::count_distinct(&nums, i + 1, n);
            out.push(p - s);
            i = i + 1;
        }
        out
    }
}
