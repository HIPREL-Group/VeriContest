impl Solution {
    pub fn can_measure_water(x: i32, y: i32, target: i32) -> bool {
        let x_u: u32 = x as u32;
        let y_u: u32 = y as u32;
        let target_u: u32 = target as u32;
        if target_u > x_u + y_u {
            return false;
        }
        let mut a: u32 = x_u;
        let mut b: u32 = y_u;
        while b != 0 {
            let rem: u32 = a % b;
            a = b;
            b = rem;
        }
        target_u % a == 0
    }
}
