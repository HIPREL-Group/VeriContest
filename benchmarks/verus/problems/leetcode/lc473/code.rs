impl Solution {
    pub fn makesquare(matchsticks: Vec<i32>) -> bool
    {
        if matchsticks.len() < 4 {
            return false;
        }
        let total = Self::sum_from(&matchsticks, 0);
        if total % 4 != 0 {
            return false;
        }
        Self::search(&matchsticks, 0, 0, 0, 0, 0, total / 4)
    }

    fn sum_from(matchsticks: &Vec<i32>, index: usize) -> i32
    {
        if index == matchsticks.len() {
            0
        } else {
            let rest = Self::sum_from(matchsticks, index + 1);
            matchsticks[index] + rest
        }
    }

    fn search(matchsticks: &Vec<i32>, index: usize, side0: i32, side1: i32, side2: i32, side3: i32, target: i32) -> bool
    {
        if index == matchsticks.len() {
            return side0 == target && side1 == target && side2 == target && side3 == target;
        }
        let x = matchsticks[index];
        let found0 = if x <= target - side0 {
            let r = Self::search(matchsticks, index + 1, side0 + x, side1, side2, side3, target);
            if r {
                return true;
            }
            r
        } else {
            false
        };
        let found1 = if side1 != side0 && x <= target - side1 {
            let r = Self::search(matchsticks, index + 1, side0, side1 + x, side2, side3, target);
            if r {
                return true;
            }
            r
        } else {
            false
        };
        let found2 = if side2 != side0 && side2 != side1 && x <= target - side2 {
            let r = Self::search(matchsticks, index + 1, side0, side1, side2 + x, side3, target);
            if r {
                return true;
            }
            r
        } else {
            false
        };
        let found3 = if side3 != side0 && side3 != side1 && side3 != side2 && x <= target - side3 {
            let r = Self::search(matchsticks, index + 1, side0, side1, side2, side3 + x, target);
            if r {
                return true;
            }
            r
        } else {
            false
        };
        false
    }
}
