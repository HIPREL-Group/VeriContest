use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn vlad_beautiful(a: Vec<u32>, n: usize) -> (result: bool)
        requires
            1 <= n <= 200_000,
            a.len() == n,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
        ensures
            result == (
                (forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] % 2 == 1)
                ||
                (forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] % 2 == 0)
                ||
                (exists|j: int| 0 <= j < a.len() && #[trigger] a[j] % 2 == 1 &&
                    (forall|i: int| 0 <= i < a.len() && a[i] % 2 == 0 ==> #[trigger] a[i] > a[j]))
            ),
    {
        let mut min_even: u64 = u64::MAX;
        let mut min_odd: u64 = u64::MAX;
        let mut min_even_idx: usize = 0;
        let mut min_odd_idx: usize = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 200_000,
                a.len() == n,
                forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 1_000_000_000,
                0 <= i <= n,
                
                (min_even == u64::MAX) <==> (forall|k: int| 0 <= k < i ==> #[trigger] a[k] % 2 == 1),
                (min_odd == u64::MAX) <==> (forall|k: int| 0 <= k < i ==> #[trigger] a[k] % 2 == 0),
                min_even != u64::MAX ==> (
                    min_even_idx < i && a[min_even_idx as int] % 2 == 0 && a[min_even_idx as int] as u64 == min_even
                ),
                min_odd != u64::MAX ==> (
                    min_odd_idx < i && a[min_odd_idx as int] % 2 == 1 && a[min_odd_idx as int] as u64 == min_odd
                ),
                forall|k: int| 0 <= k < i && a[k] % 2 == 0 ==> #[trigger] (a[k] as u64) >= min_even,
                forall|k: int| 0 <= k < i && a[k] % 2 == 1 ==> #[trigger] (a[k] as u64) >= min_odd,
            decreases n - i,
        {
            let v = a[i] as u64;
            if a[i] % 2 == 0 {
                if v < min_even {
                    min_even = v;
                    min_even_idx = i;
                }
            } else {
                if v < min_odd {
                    min_odd = v;
                    min_odd_idx = i;
                }
            }
            i += 1;
        }
        
        if min_even == u64::MAX {
            
            proof {
                assert(forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] % 2 == 1);
            }
            true
        } else if min_odd == u64::MAX {
            
            proof {
                assert(forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] % 2 == 0);
            }
            true
        } else {
            
            let res = min_odd < min_even;
            if res {
                
                proof {
                    let j = min_odd_idx as int;
                    assert(0 <= j < a.len());
                    assert(a[j] % 2 == 1);
                    assert(a[j] as u64 == min_odd);
                    assert(min_odd < min_even);
                    assert forall|i2: int| 0 <= i2 < a.len() && a[i2] % 2 == 0 implies #[trigger] a[i2] > a[j] by {
                        assert((a[i2] as u64) >= min_even);
                        assert((a[i2] as u64) > min_odd);
                        assert((a[i2] as u64) > (a[j] as u64));
                    }
                }
            } else {
                
                proof {
                    
                    
                    
                    assert(min_odd >= min_even);
                    let bad_idx = min_even_idx as int;
                    assert(0 <= bad_idx < a.len());
                    assert(a[bad_idx] % 2 == 0);
                    assert(a[bad_idx] as u64 == min_even);
                    assert forall|j: int| 0 <= j < a.len() && a[j] % 2 == 1 implies #[trigger] a[j] >= a[bad_idx] by {
                        assert((a[j] as u64) >= min_odd);
                        assert((a[j] as u64) >= min_even);
                        assert((a[j] as u64) >= (a[bad_idx] as u64));
                    }
                    
                    assert(!(exists|j: int| 0 <= j < a.len() && #[trigger] a[j] % 2 == 1 &&
                        (forall|i2: int| 0 <= i2 < a.len() && a[i2] % 2 == 0 ==> #[trigger] a[i2] > a[j])));
                    
                    assert(!(forall|i2: int| 0 <= i2 < a.len() ==> #[trigger] a[i2] % 2 == 1));
                    
                    assert(!(forall|i2: int| 0 <= i2 < a.len() ==> #[trigger] a[i2] % 2 == 0));
                }
            }
            res
        }
    }
}

}
