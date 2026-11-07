use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn valid_mask(x: i32) -> bool {
    0 <= x <= 3
}

pub open spec fn feasible_cost(m: Seq<i32>, s: Seq<i32>, v: int) -> bool {
    (exists|i: int| 0 <= i < m.len() && s[i] == 3 && v == m[i] as int)
        || (exists|i: int, j: int| 0 <= i < m.len() && 0 <= j < m.len() && s[i] == 2 && s[j] == 1
            && v == m[i] as int + m[j] as int)
}

pub struct Solution;

impl Solution {
    fn min_for_mask(m: &Vec<i32>, s: &Vec<i32>, target: i32) -> (res: (i32, bool))
        requires
            m.len() == s.len(),
            1 <= m.len() <= 200_000,
            target == 1 || target == 2 || target == 3,
            forall|i: int| 0 <= i < m.len() ==> 1 <= #[trigger] m[i] <= 200_000,
            forall|i: int| 0 <= i < s.len() ==> valid_mask(#[trigger] s[i]),
        ensures
            res.1 <==> exists|i: int| 0 <= i < m.len() && s[i] == target,
            !res.1 ==> res.0 == 1_000_000_000,
            res.1 ==> exists|i: int| 0 <= i < m.len() && s[i] == target && res.0 == m[i],
            forall|i: int| 0 <= i < m.len() && s[i] == target ==> res.0 <= m[i],
    {
        let inf: i32 = 1_000_000_000;
        let n = m.len();
        let mut best = inf;
        let mut seen = false;

        let mut i: usize = 0;
        while i < n {
            if s[i] == target {
                if !seen {
                    seen = true;
                    best = m[i];
                } else if m[i] < best {
                    best = m[i];
                }
            }
            i = i + 1;
        }

        (best, seen)
    }

    pub fn min_minutes(m: Vec<i32>, s: Vec<i32>) -> (result: i32)
        requires
            1 <= m.len() <= 200_000,
            m.len() == s.len(),
            forall|i: int| 0 <= i < m.len() ==> 1 <= #[trigger] m[i] <= 200_000,
            forall|i: int| 0 <= i < s.len() ==> valid_mask(#[trigger] s[i]),
        ensures
            result == -1 ==> !exists|v: int| feasible_cost(m@, s@, v),
            result != -1 ==> feasible_cost(m@, s@, result as int),
            result != -1 ==> forall|v: int| feasible_cost(m@, s@, v) ==> result as int <= v,
    {
        let inf: i32 = 1_000_000_000;
        let n = m.len();

        let r11 = Solution::min_for_mask(&m, &s, 3);
        let r10 = Solution::min_for_mask(&m, &s, 2);
        let r01 = Solution::min_for_mask(&m, &s, 1);

        let best11 = r11.0;
        let seen11 = r11.1;
        let best10 = r10.0;
        let seen10 = r10.1;
        let best01 = r01.0;
        let seen01 = r01.1;

        let cand11 = if seen11 { best11 } else { inf };
        let candpair = if best10 < inf && best01 < inf {
            best10 + best01
        } else {
            inf
        };
        let ans = if cand11 < candpair { cand11 } else { candpair };

        if ans >= inf {
            -1
        } else {
            ans
        }
    }
}

}
