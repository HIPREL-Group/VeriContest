use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_eq(s: Seq<i32>, v: i32, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_eq(s, v, end - 1) + if s[end - 1] == v { 1int } else { 0int }
        }
    }

    pub open spec fn min_rotations(tops: Seq<i32>, bottoms: Seq<i32>, v: i32) -> int {
        let n = tops.len() as int;
        let ct = Self::count_eq(tops, v, n);
        let cb = Self::count_eq(bottoms, v, n);
        if ct >= cb { n - ct } else { n - cb }
    }

    pub open spec fn has_blocker(tops: Seq<i32>, bottoms: Seq<i32>, v: i32) -> bool {
        exists|i: int| 0 <= i < tops.len() && tops[i] != v && bottoms[i] != v
    }

    fn check_value(tops: &Vec<i32>, bottoms: &Vec<i32>, v: i32) -> (result: (bool, usize, usize, usize))
        requires
            2 <= tops.len() <= 20000,
            bottoms.len() == tops.len(),
            forall|i: int| 0 <= i < tops.len() ==> 1 <= #[trigger] tops[i] <= 6,
            forall|i: int| 0 <= i < bottoms.len() ==> 1 <= #[trigger] bottoms[i] <= 6,
            1 <= v <= 6,
        ensures
            result.0 ==> (
                forall|j: int| 0 <= j < tops.len() ==> tops@[j] == v || bottoms@[j] == v
            ),
            result.0 ==> result.1 as int == tops.len() as int - Self::count_eq(tops@, v, tops.len() as int),
            result.0 ==> result.2 as int == tops.len() as int - Self::count_eq(bottoms@, v, tops.len() as int),
            result.0 ==> result.1 <= tops.len(),
            result.0 ==> result.2 <= tops.len(),
            !result.0 ==> 0 <= result.3 < tops.len(),
            !result.0 ==> tops@[result.3 as int] != v && bottoms@[result.3 as int] != v,
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

    pub fn min_domino_rotations(tops: Vec<i32>, bottoms: Vec<i32>) -> (result: i32)
        requires
            2 <= tops.len() <= 20000,
            bottoms.len() == tops.len(),
            forall|i: int| 0 <= i < tops.len() ==> 1 <= #[trigger] tops[i] <= 6,
            forall|i: int| 0 <= i < bottoms.len() ==> 1 <= #[trigger] bottoms[i] <= 6,
        ensures
            result == -1 || result >= 0,
            result != -1 ==> exists|v: i32| 1 <= v <= 6 && (
                forall|i: int| 0 <= i < tops.len() ==> tops@[i] == v || bottoms@[i] == v
            ) && result as int == Self::min_rotations(tops@, bottoms@, v),
            result == -1 ==> forall|v: i32| 1 <= v <= 6 ==>
                #[trigger] Self::has_blocker(tops@, bottoms@, v),
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

}
