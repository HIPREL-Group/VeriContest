use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn hour12_spec(h24: int) -> int
    recommends 0 <= h24 <= 23,
{
    if h24 == 0 {
        12
    } else if h24 <= 11 {
        h24
    } else if h24 == 12 {
        12
    } else {
        h24 - 12
    }
}

impl Solution {
    pub fn convert_hour(h24: u8) -> (result: (u8, bool))
        requires
            h24 <= 23,
        ensures
            1 <= result.0 <= 12,
            result.1 == (h24 >= 12),
            (h24 == 0 ==> result.0 == 12),
            (1 <= h24 <= 11 ==> result.0 == h24),
            (h24 == 12 ==> result.0 == 12),
            (13 <= h24 <= 23 ==> result.0 == h24 - 12),
    {
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

    pub fn convert_time(h24: u8, minute: u8) -> (result: Vec<u8>)
        requires
            h24 <= 23,
            minute <= 59,
        ensures
            result.len() == 8,
            result[0] as int == 48 + hour12_spec(h24 as int) / 10,
            result[1] as int == 48 + hour12_spec(h24 as int) % 10,
            result[2] == 58u8,
            result[3] as int == 48 + (minute as int) / 10,
            result[4] as int == 48 + (minute as int) % 10,
            result[5] == 32u8,
            result[6] == if h24 >= 12 { 80u8 } else { 65u8 },
            result[7] == 77u8,
    {
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

}
