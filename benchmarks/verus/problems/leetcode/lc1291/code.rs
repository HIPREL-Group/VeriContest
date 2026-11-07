impl Solution {
    pub fn sequential_digits(low: i32, high: i32) -> Vec<i32>
    {
        let candidates = [
            12i32, 23, 34, 45, 56, 67, 78, 89,
            123, 234, 345, 456, 567, 678, 789,
            1234, 2345, 3456, 4567, 5678, 6789,
            12345, 23456, 34567, 45678, 56789,
            123456, 234567, 345678, 456789,
            1234567, 2345678, 3456789,
            12345678, 23456789,
            123456789,
        ];

        let mut result: Vec<i32> = Vec::new();
        let mut i = 0;
        while i < candidates.len()
        {
            let x = candidates[i];
            if low <= x && x <= high {
                result.push(x);
            }
            i += 1;
        }
        result
    }
}
