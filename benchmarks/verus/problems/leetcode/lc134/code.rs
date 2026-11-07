impl Solution {
    pub fn can_complete_circuit(gas: Vec<i32>, cost: Vec<i32>) -> i32
    {
        let n = gas.len();
        let mut total: i64 = 0;
        let mut tank: i64 = 0;
        let mut start: usize = 0;

        let mut i: usize = 0;
        while i < n
        {
            let gain = gas[i] as i64 - cost[i] as i64;

            total = total + gain;
            tank = tank + gain;

            if tank < 0 {
                tank = 0;
                start = i + 1;
            } 

            i = i + 1;
        }

        if total < 0 {
            -1
        } else {
            if start == n {
                0
            } else {
                start as i32
            }
        }
    }
}
