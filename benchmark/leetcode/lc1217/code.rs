impl Solution {
    pub fn min_cost_to_move_chips(position: Vec<i32>) -> i32
    {
        let n = position.len();
        let mut odd_count: i32 = 0;
        let mut i: usize = 0;
        while i < n
        {
            if position[i] % 2 != 0 {
                odd_count = odd_count + 1;
            }
            i = i + 1;
        }
        let even_count = n as i32 - odd_count;
        if odd_count <= even_count {
            odd_count
        } else {
            even_count
        }
    }
}
