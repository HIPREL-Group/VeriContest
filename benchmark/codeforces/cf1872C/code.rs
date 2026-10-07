impl Solution {
    pub fn non_coprime_split(l: i32, r: i32) -> Option<(i32, i32)> {
        let mut s = l;
        while s <= r {
            if s >= 4 {
                if s % 2 == 0 {
                    return Some((2, s - 2));
                }
                let mut d: i32 = 3;
                while d <= s / d {
                    if s % d == 0 {
                        return Some((d, s - d));
                    }
                    d = d + 2;
                }
            }
            s = s + 1;
        }
        None
    }
}
