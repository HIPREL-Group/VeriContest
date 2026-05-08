use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_gcd(a: nat, b: nat) -> nat
        decreases b
    {
        if b == 0 { a } else { Self::spec_gcd(b, a % b) }
    }

    pub open spec fn spec_divides_both(d: int, x: int, y: int) -> bool {
        x % d == 0 && y % d == 0
    }

    pub open spec fn spec_coprime_values(x: int, y: int) -> bool {
        x >= 1 && y >= 1 && Self::spec_gcd(x as nat, y as nat) == 1
    }

    pub open spec fn spec_last_pos_prefix(a: Seq<i32>, v: int, i: int) -> int
        decreases i
    {
        if i <= 0 {
            -1
        } else {
            let prev = Self::spec_last_pos_prefix(a, v, i - 1);
            if a[i - 1] as int == v {
                i
            } else {
                prev
            }
        }
    }

    pub open spec fn spec_last_pos(a: Seq<i32>, v: int) -> int {
        Self::spec_last_pos_prefix(a, v, a.len() as int)
    }

    pub open spec fn spec_pair_score(a: Seq<i32>, x: int, y: int) -> int {
        let px = Self::spec_last_pos(a, x);
        let py = Self::spec_last_pos(a, y);
        if px >= 1 && py >= 1 && Self::spec_coprime_values(x, y) {
            px + py
        } else {
            -1
        }
    }

    pub open spec fn spec_optimal_answer(a: Seq<i32>, res: int) -> bool {
        &&& forall|x: int, y: int|
            1 <= x <= 1000 && 1 <= y <= 1000 ==> Self::spec_pair_score(a, x, y) <= res
        &&& (res == -1 || exists|x: int, y: int|
            1 <= x <= 1000 && 1 <= y <= 1000 && Self::spec_pair_score(a, x, y) == res)
    }

    pub fn is_coprime_values(x: i32, y: i32) -> (res: bool)
        requires
            1 <= x <= 1000,
            1 <= y <= 1000,
        ensures
            res == Self::spec_coprime_values(x as int, y as int),
    {
        let mut a = x;
        let mut b = y;
        while b != 0 {
            let r = a % b;
            a = b;
            b = r;
        }
        a == 1
    }

    pub fn max_coprime_index_sum(a: Vec<i32>) -> (res: i32)
        requires
            2 <= a.len() <= 200000,
            forall|j: int| 0 <= j < a.len() as int ==> 1 <= #[trigger] a[j] <= 1000,
        ensures
            Self::spec_optimal_answer(a@, res as int),
    {
        let n = a.len();
        let mut last: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < 1001 {
            last.push(-1);
            k = k + 1;
        }

        let mut i: usize = 0;
        while i < n {
            let v = a[i] as usize;
            last.set(v, i as i32 + 1);
            i = i + 1;
        }

        let mut ans: i32 = -1;
        let mut x: i32 = 1;
        while x <= 1000 {
            let mut y: i32 = 1;
            while y <= 1000 {
                let cop = Self::is_coprime_values(x, y);
                let lx = last[x as usize];
                let ly = last[y as usize];
                if lx != -1 && ly != -1 && cop {
                    let cand = lx + ly;
                    if cand > ans {
                        ans = cand;
                    }
                }
                y = y + 1;
            }
            x = x + 1;
        }

        ans
    }
}

}
