impl Solution {
    pub fn is_pangram(n: usize, s: Vec<u8>) -> bool {
        let mut present = Vec::new();
        let mut j = 0usize;
        while j < 26 {
            present.push(false);
            j = j + 1;
        }
        let mut i = 0usize;
        while i < n {
            let b = s[i];
            let idx = if b >= 65u8 && b <= 90u8 {
                (b - 65u8) as usize
            } else {
                (b - 97u8) as usize
            };
            present[idx] = true;
            i = i + 1;
        }
        let mut k = 0usize;
        let mut all = true;
        while k < 26 {
            if !present[k] {
                all = false;
            }
            k = k + 1;
        }
        all
    }
}
