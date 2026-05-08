impl Solution {
    pub const KM_PER_LITER: i32 = 10;

    pub fn distance_traveled(main_tank: i32, additional_tank: i32) -> i32 {
        if main_tank < 5 || additional_tank == 0 {
            main_tank * Self::KM_PER_LITER
        } else {
            5 * Self::KM_PER_LITER + Self::distance_traveled(main_tank - 4, additional_tank - 1)
        }
    }
}
