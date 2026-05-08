impl Solution {
    pub fn number_of_employees_who_met_target(hours: Vec<i32>, target: i32) -> i32 
    {
        let mut count = 0;
        for i in 0..hours.len() 
        {
            if hours[i] >= target { count += 1; }
        }
        count
    }
}
