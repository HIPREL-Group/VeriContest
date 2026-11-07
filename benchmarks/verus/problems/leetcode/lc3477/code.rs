impl Solution {
    pub fn num_of_unplaced_fruits(fruits: Vec<i32>, baskets: Vec<i32>) -> i32 {
        let n = fruits.len();
        let mut used: Vec<i32> = vec![0; n];
        let mut unplaced: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            let fruit = fruits[i];
            let mut placed_idx: i32 = -1;
            let mut j: usize = 0;
            while j < n {
                if placed_idx == -1 && used[j] == 0 && baskets[j] >= fruit {
                    used[j] = 1;
                    placed_idx = j as i32;
                }
                j += 1;
            }
            if placed_idx == -1 {
                unplaced += 1;
            }
            i += 1;
        }
        unplaced
    }
}
