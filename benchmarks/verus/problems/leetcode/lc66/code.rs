pub fn rev<T: Copy>(v: Vec<T>) -> Vec<T> {
    let mut result: Vec<T> = Vec::with_capacity(v.len());
    let mut i = v.len();
    while i > 0 {
        i -= 1;
        result.push(v[i]);
    }
    result
}

impl Solution {
    pub fn plus_one_rev(digits: Vec<i32>) -> Vec<i32> {
        let mut carry = 1;
        let mut result: Vec<i32> = Vec::with_capacity(digits.len() + 1);
        let mut i = 0;
        while i < digits.len() {
            let digit = digits[i];
            let sum = carry + digit;
            let result_clone = result.clone();
            carry = sum / 10;
            result.push(sum % 10);
            i += 1;
        }
        let result_clone = result.clone();
        if carry == 1 {
            result.push(carry);
        }
        result
    }

    pub fn plus_one(digits: Vec<i32>) -> Vec<i32> {
        let rev_dig = rev(digits);
        let result_rev = Self::plus_one_rev(rev_dig);
        let result = rev(result_rev);
        result
    }
}
