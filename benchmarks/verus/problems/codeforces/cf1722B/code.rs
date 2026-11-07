impl Solution {
    pub fn colourblind_match(n: usize, row1: Vec<u8>, row2: Vec<u8>) -> bool {
        let mut i: usize = 0;
        while i < n {
            let a = row1[i];
            let b = row2[i];
            let na = if a == 1u8 || a == 2u8 { 1u8 } else { a };
            let nb = if b == 1u8 || b == 2u8 { 1u8 } else { b };
            if na != nb {
                return false;
            }
            i += 1;
        }
        true
    }
}
