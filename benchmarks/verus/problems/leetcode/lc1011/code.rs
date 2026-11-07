impl Solution {
    pub fn ship_within_days(weights: Vec<i32>, days: i32) -> i32
    {
        let mut max_w = weights[0];
        let mut sum_w = weights[0];
        let mut i = 1usize;
        while i < weights.len()
        {
            if weights[i] > max_w {
                max_w = weights[i];
            }
            sum_w += weights[i];
            i += 1;
        }

        let mut low = max_w;
        let mut high = sum_w;

        while low < high
        {
            let mid = low + (high - low) / 2;
            let mut need = 1;
            let mut cur = 0;
            let mut j = 0usize;
            while j < weights.len()
            {
                if cur + weights[j] > mid {
                    need += 1;
                    cur = weights[j];
                } else {
                    cur += weights[j];
                }
                j += 1;
            }

            if need <= days {
                high = mid;
            } else {
                low = mid + 1;
            }
        }

        low
    }
}
