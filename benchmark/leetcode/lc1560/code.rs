impl Solution {
    pub fn most_visited(n: i32, rounds: Vec<i32>) -> Vec<i32> {
        let start = rounds[0];
        let end_val = rounds[rounds.len() - 1];
        let mut result: Vec<i32> = Vec::new();
        if start <= end_val {
            let mut s = start;
            while s <= end_val {
                result.push(s);
                s = s + 1;
            }
        } else {
            let mut s: i32 = 1;
            while s <= end_val {
                result.push(s);
                s = s + 1;
            }
            s = start;
            while s <= n {
                result.push(s);
                s = s + 1;
            }
        }
        result
    }
}
