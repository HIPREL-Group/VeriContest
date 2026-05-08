use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_k(rating: Seq<i32>, i: int, j: int, k: int) -> int
        recommends
            0 <= i < j < k <= rating.len(),
        decreases if k > j { k - j } else { 0int },
    {
        if k <= j + 1 {
            0
        } else {
            Self::count_k(rating, i, j, k - 1) + 
            (if (rating[i] < rating[j] && rating[j] < rating[k - 1]) || 
                (rating[i] > rating[j] && rating[j] > rating[k - 1]) { 1int } else { 0int })
        }
    }

    pub open spec fn count_j(rating: Seq<i32>, i: int, j: int) -> int
        recommends
            0 <= i < j <= rating.len(),
        decreases if j > i { j - i } else { 0int },
    {
        if j <= i + 1 {
            0
        } else {
            Self::count_j(rating, i, j - 1) + Self::count_k(rating, i, j - 1, rating.len() as int)
        }
    }

    pub open spec fn count_i(rating: Seq<i32>, i: int) -> int
        recommends
            0 <= i <= rating.len(),
        decreases if i > 0 { i } else { 0int },
    {
        if i <= 0 {
            0
        } else {
            Self::count_i(rating, i - 1) + Self::count_j(rating, i - 1, rating.len() as int)
        }
    }

    pub fn num_teams(rating: Vec<i32>) -> (result: i32)
        requires
            3 <= rating.len() <= 1000,
            forall|x: int| 0 <= x < rating.len() ==> 1 <= #[trigger] rating[x] <= 100000,
        ensures
            result == Self::count_i(rating@, rating.len() as int),
    {
        let mut count: i32 = 0;
        let mut i: usize = 0;
        let n: usize = rating.len();
        
        while i < n
            invariant
                n == rating.len(),
                3 <= n <= 1000,
                0 <= i <= n,
                0 <= count <= i * 1000000,
                forall|x: int| 0 <= x < n ==> 1 <= #[trigger] rating[x] <= 100000,
                count as int == Self::count_i(rating@, i as int),
            decreases n - i,
        {
            let mut j: usize = i + 1;
            let mut inner_count_j: i32 = 0;
            
            while j < n
                invariant
                    n == rating.len(),
                    3 <= n <= 1000,
                    0 <= i < n,
                    i + 1 <= j <= n,
                    0 <= inner_count_j <= (j - (i + 1)) * 1000,
                    forall|x: int| 0 <= x < n ==> 1 <= #[trigger] rating[x] <= 100000,
                    inner_count_j as int == Self::count_j(rating@, i as int, j as int),
                decreases n - j,
            {
                let mut k: usize = j + 1;
                let mut inner_count_k: i32 = 0;
                
                while k < n
                    invariant
                        n == rating.len(),
                        3 <= n <= 1000,
                        0 <= i < j,
                        j < n,
                        j + 1 <= k <= n,
                        0 <= inner_count_k <= k - (j + 1),
                        forall|x: int| 0 <= x < n ==> 1 <= #[trigger] rating[x] <= 100000,
                        inner_count_k as int == Self::count_k(rating@, i as int, j as int, k as int),
                    decreases n - k,
                {
                    let ri = rating[i];
                    let rj = rating[j];
                    let rk = rating[k];
                    
                    if (ri < rj && rj < rk) || (ri > rj && rj > rk) {
                        inner_count_k += 1;
                    }
                    k += 1;
                }
                inner_count_j += inner_count_k;
                j += 1;
            }
            count += inner_count_j;
            i += 1;
        }
        
        count
    }
}

}
