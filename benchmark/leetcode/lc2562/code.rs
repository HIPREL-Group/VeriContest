impl Solution {
    pub fn find_the_array_conc_val(nums: Vec<i32>) -> i64 {
        let mut i: usize = 0;
        let mut j: usize = nums.len() - 1;
        let mut total: i64 = 0;

        while i < j {
            let mut mul: i64 = 10;
            let mut x = nums[j] / 10;
            while x > 0 {
                mul = mul.wrapping_mul(10);
                x = x / 10;
            }
            total = total.wrapping_add((nums[i] as i64).wrapping_mul(mul).wrapping_add(nums[j] as i64));
            i = i + 1;
            j = j - 1;
        }

        if i == j {
            total = total.wrapping_add(nums[i] as i64);
        }

        total
    }
}
