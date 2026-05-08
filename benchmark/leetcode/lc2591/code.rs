impl Solution {
    pub fn dist_money(money: i32, children: i32) -> i32 {
        if money < children {
            return -1;
        }

        let rem = money - children;
        if rem / 7 == children && rem % 7 == 0 {
            children
        } else if rem / 7 == children - 1 && rem % 7 == 3 {
            children - 2
        } else if rem / 7 < children - 1 {
            rem / 7
        } else {
            children - 1
        }
    }
}
