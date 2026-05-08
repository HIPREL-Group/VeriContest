impl Solution {
    pub fn get_winner(arr: Vec<i32>, k: i32) -> i32 {
        let mut current = arr[0];
        let mut wins: i32 = 0;
        let n = arr.len();
        let mut i: usize = 1;

        while i < n {
            if arr[i] > current {
                current = arr[i];
                wins = 1;
            } else {
                wins += 1;
            }

            if wins == k {
                return current;
            }

            i += 1;
        }

        current
    }
}
