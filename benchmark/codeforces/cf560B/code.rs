impl Solution {
    pub fn can_place_paintings(a1: i32, b1: i32, a2: i32, b2: i32, a3: i32, b3: i32) -> bool {
        let check1 = a2 + a3 <= a1 && b2 <= b1 && b3 <= b1;
        let check2 = a2 + b3 <= a1 && b2 <= b1 && a3 <= b1;
        let check3 = b2 + a3 <= a1 && a2 <= b1 && b3 <= b1;
        let check4 = b2 + b3 <= a1 && a2 <= b1 && a3 <= b1;
        let check5 = a2 <= a1 && a3 <= a1 && b2 + b3 <= b1;
        let check6 = a2 <= a1 && b3 <= a1 && b2 + a3 <= b1;
        let check7 = b2 <= a1 && a3 <= a1 && a2 + b3 <= b1;
        let check8 = b2 <= a1 && b3 <= a1 && a2 + a3 <= b1;
        let result = check1 || check2 || check3 || check4 || check5 || check6 || check7 || check8;
        result
    }
}
