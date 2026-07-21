impl Solution {
    pub fn count_tested_devices(battery_percentages: Vec<i32>) -> i32 {
        let n = battery_percentages.len();
        let mut tested = 0i32;
        let mut i = 0;
        while i < n {
            if battery_percentages[i] > tested {
                tested = tested + 1;
            }
            i = i + 1;
        }
        tested
    }
}
