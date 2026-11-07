use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    

    
    
    pub open spec fn optimal_diff(values: Seq<i32>, i: int) -> int
        decreases values.len() - i
    {
        if i >= values.len() {
            0
        } else {
            let n = values.len() as int;
            let t1 = values[i] as int - Self::optimal_diff(values, i + 1);
            if i + 1 >= n {
                t1
            } else {
                let t2 = values[i] as int + values[i + 1] as int - Self::optimal_diff(values, i + 2);
                if i + 2 >= n {
                    if t1 >= t2 { t1 } else { t2 }
                } else {
                    let t3 = values[i] as int + values[i + 1] as int + values[i + 2] as int - Self::optimal_diff(values, i + 3);
                    if t1 >= t2 && t1 >= t3 { t1 }
                    else if t2 >= t3 { t2 }
                    else { t3 }
                }
            }
        }
    }

    proof fn lemma_optimal_diff_bound(values: Seq<i32>, i: int)
        requires
            0 <= i <= values.len(),
            forall |j: int| 0 <= j < values.len() ==>
                -1000 <= #[trigger] values[j] <= 1000,
        ensures
            Self::optimal_diff(values, i) >= -(1000 * (values.len() - i)),
            Self::optimal_diff(values, i) <= 1000 * (values.len() - i),
        decreases values.len() - i
    {
        if i >= values.len() {
        } else {
            Self::lemma_optimal_diff_bound(values, i + 1);
            if i + 1 < values.len() as int {
                Self::lemma_optimal_diff_bound(values, i + 2);
            }
            if i + 2 < values.len() as int {
                Self::lemma_optimal_diff_bound(values, i + 3);
            }
        }
    }

    pub fn stone_game_iii(stone_value: Vec<i32>) -> (result: String)
        requires
            1 <= stone_value.len() <= 50_000,
            forall |i: int| 0 <= i < stone_value.len() ==>
                -1000 <= #[trigger] stone_value[i] <= 1000,
        ensures
            Self::optimal_diff(stone_value@, 0) > 0 ==> result@ == "Alice"@,
            Self::optimal_diff(stone_value@, 0) < 0 ==> result@ == "Bob"@,
            Self::optimal_diff(stone_value@, 0) == 0 ==> result@ == "Tie"@,
    {
        let n = stone_value.len();
        let mut dp: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k <= n
            invariant
                0 <= k <= n + 1,
                n <= 50_000,
                dp.len() == k,
                forall |j: int| 0 <= j < k as int ==> (#[trigger] dp@[j]) == 0i64,
            decreases n + 1 - k,
        {
            dp.push(0i64);
            k = k + 1;
        }
        let mut i: usize = n;
        while i > 0
            invariant
                0 <= i <= n,
                n == stone_value.len(),
                dp.len() == n + 1,
                1 <= stone_value.len() <= 50_000,
                forall |j: int| 0 <= j < stone_value.len() ==>
                    -1000 <= #[trigger] stone_value[j] <= 1000,
                forall |j: int| i as int <= j <= n as int ==>
                    (#[trigger] dp@[j]) as int == Self::optimal_diff(stone_value@, j),
            decreases i,
        {
            i = i - 1;
            proof {
                Self::lemma_optimal_diff_bound(stone_value@, (i + 1) as int);
                if (i as int + 1 < n as int) {
                    Self::lemma_optimal_diff_bound(stone_value@, (i + 2) as int);
                }
                if (i as int + 2 < n as int) {
                    Self::lemma_optimal_diff_bound(stone_value@, (i + 3) as int);
                }
            }
            let mut best: i64 = stone_value[i] as i64 - dp[i + 1];
            if i + 1 < n {
                let t2: i64 = stone_value[i] as i64 + stone_value[i + 1] as i64 - dp[i + 2];
                if t2 > best {
                    best = t2;
                }
            }
            if i + 2 < n {
                let t3: i64 = stone_value[i] as i64 + stone_value[i + 1] as i64 + stone_value[i + 2] as i64 - dp[i + 3];
                if t3 > best {
                    best = t3;
                }
            }
            dp.set(i, best);
            proof {
                assert(best as int == Self::optimal_diff(stone_value@, i as int));
            }
        }
        if dp[0] > 0 {
            "Alice".to_string()
        } else if dp[0] < 0 {
            "Bob".to_string()
        } else {
            "Tie".to_string()
        }
    }
}

}
