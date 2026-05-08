impl Solution {
    pub fn can_place_flowers(flowerbed: Vec<i32>, n: i32) -> bool
    {
        let len = flowerbed.len();
        let mut i: usize = 0;
        let mut count: usize = 0;
        let mut prev_planted = false;

        while i < len
        {
            if flowerbed[i] == 1 {
                prev_planted = true;
            } else {
                let next_empty = if i + 1 < len { flowerbed[i + 1] == 0 } else { true };
                if !prev_planted && next_empty {
                    count = count + 1;
                    prev_planted = true;
                } else {
                    prev_planted = false;
                }
            }
            i = i + 1;
        }

        count as i32 >= n
    }
}
