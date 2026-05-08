use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn rank_of(pref_row: Seq<i32>, u: i32) -> int
        decreases pref_row.len()
    {
        if pref_row.len() == 0 {
            0
        } else if pref_row[0] == u {
            0
        } else {
            1 + Self::rank_of(pref_row.subrange(1, pref_row.len() as int), u)
        }
    }

    pub open spec fn partner_of(x: int, pairs: Seq<Vec<i32>>) -> int
        decreases pairs.len()
    {
        if pairs.len() == 0 {
            -1
        } else if pairs.last()[0] as int == x {
            pairs.last()[1] as int
        } else if pairs.last()[1] as int == x {
            pairs.last()[0] as int
        } else {
            Self::partner_of(x, pairs.drop_last())
        }
    }

    pub open spec fn is_unhappy(x: int, n: int, preferences: Seq<Vec<i32>>, pairs: Seq<Vec<i32>>) -> bool {
        exists |u: int| 0 <= u < n && u != x
            && Self::rank_of(preferences[x]@, u as i32) < Self::rank_of(preferences[x]@, Self::partner_of(x, pairs) as i32)
            && Self::rank_of(preferences[u]@, x as i32) < Self::rank_of(preferences[u]@, Self::partner_of(u, pairs) as i32)
    }

    pub open spec fn count_unhappy(k: int, n: int, preferences: Seq<Vec<i32>>, pairs: Seq<Vec<i32>>) -> int
        decreases k
    {
        if k <= 0 {
            0
        } else {
            Self::count_unhappy(k - 1, n, preferences, pairs) +
                if Self::is_unhappy(k - 1, n, preferences, pairs) { 1int } else { 0int }
        }
    }

    pub fn unhappy_friends(n: i32, preferences: Vec<Vec<i32>>, pairs: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= n <= 500,
            n % 2 == 0,
            preferences.len() == n,
            forall |i: int| 0 <= i < n ==> (#[trigger] preferences[i]).len() == n - 1,
            forall |i: int, j: int| 0 <= i < n && 0 <= j < n - 1 ==>
                0 <= #[trigger] preferences[i][j] <= n - 1,
            forall |i: int, j: int| 0 <= i < n && 0 <= j < n - 1 ==>
                preferences[i][j] != i as i32,
            forall |i: int, j1: int, j2: int| 0 <= i < n && 0 <= j1 < n - 1 && 0 <= j2 < n - 1 && j1 != j2 ==>
                #[trigger] preferences[i][j1] != #[trigger] preferences[i][j2],
            forall |i: int, u: int| #![trigger preferences[i], preferences[u]]
                0 <= i < n && 0 <= u < n && u != i ==>
                exists |j: int| 0 <= j < n - 1 && preferences[i][j] == u as i32,
            pairs.len() == n / 2,
            forall |k: int| 0 <= k < n / 2 ==>
                (#[trigger] pairs[k]).len() == 2
                && 0 <= pairs[k][0] <= n - 1
                && 0 <= pairs[k][1] <= n - 1
                && pairs[k][0] != pairs[k][1],
            forall |k1: int, k2: int| 0 <= k1 < k2 < n / 2 ==>
                (#[trigger] pairs[k1])[0] != (#[trigger] pairs[k2])[0]
                && pairs[k1][0] != pairs[k2][1]
                && pairs[k1][1] != pairs[k2][0]
                && pairs[k1][1] != pairs[k2][1],
            forall |x: int| #![trigger preferences[x]]
                0 <= x < n ==>
                exists |k: int| 0 <= k < n / 2 && (pairs[k][0] as int == x || pairs[k][1] as int == x),
        ensures
            0 <= result <= n,
            result as int == Self::count_unhappy(n as int, n as int, preferences@, pairs@),
    {
        let mut rank: Vec<i32> = Vec::new();
        let mut idx = 0;
        while idx < n * n {
            rank.push(0);
            idx = idx + 1;
        }
        let mut i = 0;
        while i < n {
            let mut j = 0;
            while j < n - 1 {
                let p = preferences[i as usize][j as usize];
                rank.set((i * n + p) as usize, j);
                j = j + 1;
            }
            i = i + 1;
        }
        let mut partner: Vec<i32> = Vec::new();
        idx = 0;
        while idx < n {
            partner.push(0);
            idx = idx + 1;
        }
        let mut k = 0;
        while k < n / 2 {
            let a = pairs[k as usize][0];
            let b = pairs[k as usize][1];
            partner.set(a as usize, b);
            partner.set(b as usize, a);
            k = k + 1;
        }
        let mut count = 0;
        i = 0;
        while i < n {
            let mut u = 0;
            let mut found = false;
            while u < n && !found {
                if u != i {
                    if rank[(i * n + u) as usize] < rank[(i * n + partner[i as usize]) as usize]
                        && rank[(u * n + i) as usize] < rank[(u * n + partner[u as usize]) as usize]
                    {
                        found = true;
                    }
                }
                u = u + 1;
            }
            if found {
                count = count + 1;
            }
            i = i + 1;
        }
        count
    }
}

}
