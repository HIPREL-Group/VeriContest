impl Solution {
    pub fn min_costs(cost: Vec<i32>) -> Vec<i32> {
        let n = cost.len();
        let mut answer: Vec<i32> = vec![0i32; n];
        let mut min_cost: i32 = cost[0];
        answer[0] = min_cost;
        let mut i: usize = 1;
        while i < n {
            if cost[i] < min_cost {
                min_cost = cost[i];
            }
            answer[i] = min_cost;
            i += 1;
        }
        answer
    }
}
