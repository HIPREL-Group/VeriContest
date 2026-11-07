impl Solution {
    pub fn perfect_permutation(n: u32) -> Option<Vec<u32>> {
        if n % 2 != 0 {
            return None;
        }
        let mut result: Vec<u32> = Vec::new();
        let mut i: u32 = 0;
        while i < n {
            if i % 2 == 0 {
                result.push(i + 2);
            } else {
                result.push(i);
            }
            i = i + 1;
        }
        Some(result)
    }
}
