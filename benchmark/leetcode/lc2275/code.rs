impl Solution {
    fn count_for_bit(candidates: &Vec<i32>, bit: i32) -> i32 {
        let mut i: usize = 0;
        let mut count: i32 = 0;
        while i < candidates.len() {
            if ((candidates[i] >> bit) & 1) == 1 {
                count = count + 1;
            }
            i = i + 1;
        }
        count
    }

    pub fn largest_combination(candidates: Vec<i32>) -> i32 {
        let mut bit: i32 = 0;
        let mut best: i32 = 0;
        while bit < 31 {
            let cur = Self::count_for_bit(&candidates, bit);
            if cur > best {
                best = cur;
            }
            bit = bit + 1;
        }
        best
    }
}
