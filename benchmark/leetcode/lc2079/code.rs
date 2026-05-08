impl Solution {
    pub fn watering_plants(plants: Vec<i32>, capacity: i32) -> i32 {
        let mut steps: i32 = 0;
        let mut current_water: i32 = capacity;
        let mut i: usize = 0;
        let n: usize = plants.len();
        
        while i < n {
            if current_water < plants[i] {
                steps += (2 * i + 1) as i32;
                current_water = capacity - plants[i];
            } else {
                steps += 1;
                current_water -= plants[i];
            }
            i += 1;
        }
        
        steps
    }
}
