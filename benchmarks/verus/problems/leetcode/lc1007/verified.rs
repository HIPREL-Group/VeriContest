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

    proof fn count_eq_bounds(s: Seq<i32>, v: i32, end: int)
        requires
            0 <= end <= s.len(),
        ensures
            0 <= Self::count_eq(s, v, end) <= end,
        decreases end,
    {
        if end > 0 {
            Self::count_eq_bounds(s, v, end - 1);
        }
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
            invariant
                0 <= i <= n,
                n == tops.len(),
                n == bottoms.len(),
                2 <= n <= 20000,
                1 <= v <= 6,
                forall|j: int| 0 <= j < tops.len() ==> 1 <= #[trigger] tops[j] <= 6,
                forall|j: int| 0 <= j < bottoms.len() ==> 1 <= #[trigger] bottoms[j] <= 6,
                rot_top as int == i as int - Self::count_eq(tops@, v, i as int),
                rot_bot as int == i as int - Self::count_eq(bottoms@, v, i as int),
                forall|j: int| 0 <= j < i ==> tops@[j] == v || bottoms@[j] == v,
                rot_top <= i,
                rot_bot <= i,
            decreases n - i,
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
            proof {
                Self::count_eq_bounds(tops@, v1, n as int);
                Self::count_eq_bounds(bottoms@, v1, n as int);
                assert(1 <= v1 <= 6);
                assert(forall|j: int| 0 <= j < tops.len() ==> tops@[j] == v1 || bottoms@[j] == v1);
                assert(r as int == Self::min_rotations(tops@, bottoms@, v1));
            }
            return r;
        }

        let v2 = bottoms[0];
        let (ok2, rt2, rb2, f2) = Self::check_value(&tops, &bottoms, v2);

        if ok2 {
            let r = if rt2 < rb2 { rt2 as i32 } else { rb2 as i32 };
            proof {
                Self::count_eq_bounds(tops@, v2, n as int);
                Self::count_eq_bounds(bottoms@, v2, n as int);
                assert(1 <= v2 <= 6);
                assert(forall|j: int| 0 <= j < tops.len() ==> tops@[j] == v2 || bottoms@[j] == v2);
                assert(r as int == Self::min_rotations(tops@, bottoms@, v2));
            }
            return r;
        }

        proof {
            assert forall|v: i32| 1 <= v <= 6 implies
                #[trigger] Self::has_blocker(tops@, bottoms@, v)
            by {
                if v == v1 {
                    assert(0 <= f1 as int && (f1 as int) < tops@.len());
                    assert(tops@[f1 as int] != v && bottoms@[f1 as int] != v);
                } else if v == v2 {
                    assert(0 <= f2 as int && (f2 as int) < tops@.len());
                    assert(tops@[f2 as int] != v && bottoms@[f2 as int] != v);
                } else {
                    assert(tops@[0] == v1 && v1 != v);
                    assert(bottoms@[0] == v2 && v2 != v);
                    assert(tops@[0] != v && bottoms@[0] != v);
                }
            }
        }
        -1
    }
}

}
