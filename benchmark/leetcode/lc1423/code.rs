impl Solution {
    pub fn max_score(card_points: Vec<i32>, k: i32) -> i32
    {
        let n = card_points.len();
        let k = k as usize;
        let mut left_sum = 0i32;
        let mut right_sum = 0i32;
        let mut i = 0usize;
        while i < k
        {
            left_sum = left_sum + card_points[i];
            i = i + 1;
        }

        let mut best = left_sum;

        let mut i = 0usize;
        while i < k
        {
            let left_card_idx = k - 1 - i;
            let right_card_idx = n - 1 - i;
            left_sum = left_sum - card_points[left_card_idx];
            right_sum = right_sum + card_points[right_card_idx];

            let score = left_sum + right_sum;
            if left_sum + right_sum > best {
                best = left_sum + right_sum;
            }
            i = i + 1;
        }

        best
    }
}
