impl Solution {
    pub fn generate_key(num1: i32, num2: i32, num3: i32) -> i32 {
        let a1 = (num1 / 1000) % 10;
        let b1 = (num2 / 1000) % 10;
        let c1 = (num3 / 1000) % 10;
        let d1 = if a1 <= b1 && a1 <= c1 {
            a1
        } else if b1 <= a1 && b1 <= c1 {
            b1
        } else {
            c1
        };

        let a2 = (num1 / 100) % 10;
        let b2 = (num2 / 100) % 10;
        let c2 = (num3 / 100) % 10;
        let d2 = if a2 <= b2 && a2 <= c2 {
            a2
        } else if b2 <= a2 && b2 <= c2 {
            b2
        } else {
            c2
        };

        let a3 = (num1 / 10) % 10;
        let b3 = (num2 / 10) % 10;
        let c3 = (num3 / 10) % 10;
        let d3 = if a3 <= b3 && a3 <= c3 {
            a3
        } else if b3 <= a3 && b3 <= c3 {
            b3
        } else {
            c3
        };

        let a4 = num1 % 10;
        let b4 = num2 % 10;
        let c4 = num3 % 10;
        let d4 = if a4 <= b4 && a4 <= c4 {
            a4
        } else if b4 <= a4 && b4 <= c4 {
            b4
        } else {
            c4
        };

        ((d1 * 10 + d2) * 10 + d3) * 10 + d4
    }
}
