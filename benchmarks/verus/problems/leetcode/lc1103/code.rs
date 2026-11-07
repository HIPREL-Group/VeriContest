impl Solution {
    pub fn distribute_candies(candies: i32, num_people: i32) -> Vec<i32> {
        let n = num_people as usize;
        let mut result: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n {
            result.push(0i32);
            idx = idx + 1;
        }
        let mut remaining = candies;
        let mut step: i32 = 0;
        while remaining > 0 {
            let give: i32 = if remaining < step + 1 { remaining } else { step + 1 };
            let person_idx: i32 = step % num_people;
            let person: usize = person_idx as usize;
            let old_val: i32 = result[person];
            result[person] = old_val + give;
            remaining = remaining - give;
            step = step + 1;
        }
        result
    }
}
