use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contains_prefix(s: Seq<i32>, x: i32, len: int) -> bool
        recommends
            0 <= len <= s.len(),
        decreases len,
    {
        if len <= 0 {
            false
        } else {
            Self::contains_prefix(s, x, len - 1) || s[len - 1] == x
        }
    }

    pub open spec fn contains(s: Seq<i32>, x: i32) -> bool {
        Self::contains_prefix(s, x, s.len() as int)
    }

    pub open spec fn greedy_from(cur: int, n: int, remain: int, banned: Seq<i32>) -> int
        decreases if cur <= n { n - cur + 1 } else { 0int },
    {
        if cur > n || remain <= 0 {
            0
        } else if Self::contains(banned, cur as i32) {
            Self::greedy_from(cur + 1, n, remain, banned)
        } else if cur <= remain {
            1 + Self::greedy_from(cur + 1, n, remain - cur, banned)
        } else {
            0
        }
    }

    pub fn max_count(banned: Vec<i32>, n: i32, max_sum: i32) -> (result: i32)
        requires
            1 <= banned.len() <= 10_000,
            1 <= n <= 10_000,
            1 <= max_sum <= 1_000_000_000,
            forall |i: int| 0 <= i < banned.len() ==> 1 <= #[trigger] banned[i] <= 10_000,
        ensures
            result == Self::greedy_from(1, n as int, max_sum as int, banned@),
    {
        let mut count: i32 = 0;
        let mut remain: i32 = max_sum;
        let mut x: i32 = 1;

        while x <= n
            invariant
                1 <= n <= 10_000,
                0 <= count,
                0 <= remain <= max_sum,
                1 <= x <= n + 1,
                count <= x - 1,
                count as int + Self::greedy_from(x as int, n as int, remain as int, banned@)
                    == Self::greedy_from(1, n as int, max_sum as int, banned@),
            decreases n - x + 1,
        {
            let mut is_banned: bool = false;
            let mut j: usize = 0;
            while j < banned.len()
                invariant
                    0 <= j <= banned.len(),
                    is_banned == Self::contains_prefix(banned@, x, j as int),
                decreases banned.len() - j,
            {
                if banned[j] == x {
                    is_banned = true;
                }
                j = j + 1;
            }

            if is_banned {
                proof {
                    assert(Self::contains_prefix(banned@, x, banned.len() as int) == Self::contains(banned@, x));
                    assert(Self::greedy_from(x as int, n as int, remain as int, banned@)
                        == Self::greedy_from((x + 1) as int, n as int, remain as int, banned@));
                }
                x = x + 1;
                continue;
            }

            if x <= remain {
                proof {
                    assert(!Self::contains(banned@, x));
                    assert(Self::greedy_from(x as int, n as int, remain as int, banned@)
                        == 1 + Self::greedy_from((x + 1) as int, n as int, (remain - x) as int, banned@));
                    assert(count <= x - 1);
                    assert(x <= n);
                    assert(n <= 10_000);
                    assert(count + 1 <= 10_000);
                    assert(count + 1 < 2_147_483_647);
                }
                remain = remain - x;
                count = count + 1;
                x = x + 1;
            } else {
                x = n + 1;
            }
        }

        count
    }
}

}
