impl Solution {
    pub fn closest_divisors(num: i32) -> Vec<i32> {
        let mut i: i32 = 2;
        while i * i <= num + 2 {
            i += 1;
        }
        i -= 1;

        let mut best_a: i32 = 1;
        let mut best_b: i32 = num + 1;
        let mut found = false;

        while i >= 1 && !found {
            let n1 = num + 1;
            let n2 = num + 2;

            if n1 % i == 0 {
                best_a = i;
                best_b = n1 / i;
                found = true;
            } else if n2 % i == 0 {
                best_a = i;
                best_b = n2 / i;
                found = true;
            }

            if !found {
                i -= 1;
            }
        }

        vec![best_a, best_b]
    }
}
