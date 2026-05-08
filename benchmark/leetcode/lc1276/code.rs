impl Solution {
    pub fn num_of_burgers(tomato_slices: i32, cheese_slices: i32) -> Vec<i32> {
        if tomato_slices % 2 != 0 {
            return Vec::new();
        }
        let jumbo = tomato_slices / 2 - cheese_slices;
        let small = cheese_slices - jumbo;
        if jumbo < 0 || small < 0 {
            return Vec::new();
        }
        let mut result = Vec::new();
        result.push(jumbo);
        result.push(small);
        result
    }
}
