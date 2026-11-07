impl Solution {
    pub fn matching_numbers(n: i32) -> Option<Vec<(i32, i32)>> {
        if n % 2 == 0 {
            return None;
        }
        let k: i32 = (3 * n + 3) / 2;
        let mut out: Vec<(i32, i32)> = Vec::new();
        let mut i: i32 = 1;
        while i <= (n + 1) / 2 {
            let a1: i32 = 2 * i - 1;
            let b1: i32 = k - i;
            out.push((a1, b1));
            i = i + 1;
        }
        let mut j: i32 = 1;
        while j <= (n - 1) / 2 {
            let a2: i32 = 2 * j;
            let b2: i32 = k + (n + 1) / 2 - j - 1;
            out.push((a2, b2));
            j = j + 1;
        }
        Some(out)
    }
}
