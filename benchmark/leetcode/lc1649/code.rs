impl Solution {
    pub fn create_sorted_array(instructions: Vec<i32>) -> i32 {
        let mut cost: i64 = 0;
        let n = instructions.len();
        let mut i: usize = 0;
        while i < n {
            let mut less: i64 = 0;
            let mut greater: i64 = 0;
            let mut j: usize = 0;
            while j < i {
                if instructions[j] < instructions[i] {
                    less = less + 1;
                }
                if instructions[j] > instructions[i] {
                    greater = greater + 1;
                }
                j = j + 1;
            }
            let min_cost: i64 = if less < greater { less } else { greater };
            cost = cost + min_cost;
            i = i + 1;
        }
        (cost % 1_000_000_007) as i32
    }
}
