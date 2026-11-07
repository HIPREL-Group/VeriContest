impl Solution {
    pub fn two_sum(numbers: Vec<i32>, target: i32) -> Vec<i32>
    {
        let mut res: Vec<i32> = vec![1, 2];
        let mut first: usize = 0;
        let mut second: usize = numbers.len() - 1;
        
        let mut solution_found: bool = false;

        while first < second && !solution_found
        {
            if numbers[first] + numbers[second] == target {
                res[0] = first as i32 + 1; 
                res[1] = second as i32 + 1; 
                solution_found = true;
            } else if numbers[first] + numbers[second] < target {
                first += 1;
            } else {
                second -= 1;
            }
        }        
        
        res
    }
}
