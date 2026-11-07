impl Solution {
    fn sum_with_speed(piles: &Vec<i32>, speed: i32) -> i64
    {
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < piles.len()
        {
            let pile: i32 = piles[i];
            let p: i64 = pile as i64;
            let s: i64 = speed as i64;
            let term: i64 = (p + s - 1) / s;
            sum += term;
            i += 1;
        }
        sum
    }

    pub fn min_eating_speed(piles: Vec<i32>, h: i32) -> i32
    {
        let mut max_pile = piles[0];
        let mut i: usize = 1;
        while i < piles.len()
        {
            if piles[i] > max_pile {
                max_pile = piles[i];
            }
            i += 1;
        }

        let mut left: i32 = 1;
        let mut right: i32 = max_pile;

        while left < right
        {
            let mid = left + (right - left) / 2;
            let s = Self::sum_with_speed(&piles, mid);
            if s <= h as i64 {
                right = mid;
            } else {
                left = mid + 1;
            }
        }

        left
    }
}
