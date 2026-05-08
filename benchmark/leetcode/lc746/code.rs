impl Solution {
    pub fn min_cost_climbing_stairs(cost: Vec<i32>) -> i32
    {
        let n = cost.len();
        let (mut a, mut b) = (cost[0], cost[1]);
        for i in 2..n 
        { 
            let c = cost[i] + if a < b { a } else { b };
            a = b;
            b = c;
        }
        if a < b { a } else { b }
    }
}
