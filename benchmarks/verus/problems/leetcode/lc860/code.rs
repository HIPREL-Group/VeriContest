impl Solution {
    pub fn lemonade_change(bills: Vec<i32>) -> bool {
        let mut five: usize = 0;
        let mut ten: usize = 0;
        let mut i: usize = 0;
        while i < bills.len() {
            let bill = bills[i];
            if bill == 5 {
                five = five + 1;
            } else if bill == 10 {
                if five == 0 {
                    return false;
                }
                five = five - 1;
                ten = ten + 1;
            } else {
                if ten > 0 && five > 0 {
                    ten = ten - 1;
                    five = five - 1;
                } else if five >= 3 {
                    five = five - 3;
                } else {
                    return false;
                }
            }
            i = i + 1;
        }
        true
    }
}
