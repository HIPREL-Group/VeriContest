pub struct CustomFunction {
    pub values: Vec<Vec<i32>>,
}

impl CustomFunction {
    pub fn f(&self, x: i32, y: i32) -> i32 {
        self.values[x as usize][y as usize]
    }
}

impl Solution {
    pub fn find_solution(customfunction: &CustomFunction, z: i32) -> Vec<Vec<i32>> {
        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut x: usize = 1;
        let mut y: usize = 1000;
        while x <= 1000 && y >= 1 {
            let val = customfunction.f(x as i32, y as i32);
            if val == z {
                let mut pair: Vec<i32> = Vec::new();
                pair.push(x as i32);
                pair.push(y as i32);
                result.push(pair);
                x = x + 1;
                y = y - 1;
            } else if val < z {
                x = x + 1;
            } else {
                y = y - 1;
            }
        }
        result
    }
}
