impl Solution {
    pub fn convert_hour(h24: u8) -> (u8, bool) {
        if h24 == 0 {
            (12, false)
        } else if h24 < 12 {
            (h24, false)
        } else if h24 == 12 {
            (12, true)
        } else {
            (h24 - 12, true)
        }
    }

    pub fn convert_time(h24: u8, minute: u8) -> Vec<u8> {
        let (h12, is_pm) = Self::convert_hour(h24);
        let mut out = Vec::new();
        out.push(48u8 + h12 / 10);
        out.push(48u8 + h12 % 10);
        out.push(58u8);
        out.push(48u8 + minute / 10);
        out.push(48u8 + minute % 10);
        out.push(32u8);
        out.push(if is_pm { 80u8 } else { 65u8 });
        out.push(77u8);
        out
    }
}
