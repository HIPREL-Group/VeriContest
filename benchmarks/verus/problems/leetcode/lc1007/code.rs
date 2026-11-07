impl Solution {
    fn check_value(tops: &Vec<i32>, bottoms: &Vec<i32>, v: i32) -> (bool, usize, usize, usize)
    {
        let n = tops.len();
        let mut rot_top: usize = 0;
        let mut rot_bot: usize = 0;
        let mut i: usize = 0;
        let mut fail_idx: usize = 0;

        while i < n
        {
            if tops[i] != v && bottoms[i] != v {
                return (false, rot_top, rot_bot, i);
            }
            if tops[i] != v { rot_top = rot_top + 1; }
            if bottoms[i] != v { rot_bot = rot_bot + 1; }
            i = i + 1;
        }
        (true, rot_top, rot_bot, 0)
    }

    pub fn min_domino_rotations(tops: Vec<i32>, bottoms: Vec<i32>) -> i32
    {
        let n = tops.len();
        let v1 = tops[0];
        let (ok1, rt1, rb1, f1) = Self::check_value(&tops, &bottoms, v1);

        if ok1 {
            let r = if rt1 < rb1 { rt1 as i32 } else { rb1 as i32 };
            return r;
        }

        let v2 = bottoms[0];
        let (ok2, rt2, rb2, f2) = Self::check_value(&tops, &bottoms, v2);

        if ok2 {
            let r = if rt2 < rb2 { rt2 as i32 } else { rb2 as i32 };
            return r;
        }

        -1
    }
}
