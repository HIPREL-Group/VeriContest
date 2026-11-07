use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn is_valid_decrements(n: usize, a: Seq<i32>, b: Seq<i32>, max_diff: i32) -> bool {
    (forall|i: int| 0 <= i && i < n ==> a[i] >= b[i]) &&
    (forall|i: int| 0 <= i && i < n ==> a[i] - b[i] <= max_diff) &&
    (forall|i: int| 0 <= i && i < n ==>
        (a[i] - b[i] == max_diff || b[i] == 0))
}

pub open spec fn has_valid_decrements(n: usize, a: Seq<i32>, b: Seq<i32>) -> bool {
    exists|max_diff: i32| max_diff >= 0 && is_valid_decrements(n, a, b, max_diff)
}

pub struct Solution;

impl Solution {
    pub fn is_possible(n: usize, a: Vec<i32>, b: Vec<i32>) -> (res: bool)
        requires
            1 <= n && n <= 50000,
            a.len() == n,
            b.len() == n,
            forall|i: int| 0 <= i && i < n ==> 0 <= a@[i] && a@[i] <= 1000000000,
            forall|i: int| 0 <= i && i < n ==> 0 <= b@[i] && b@[i] <= 1000000000,
        ensures
            res == has_valid_decrements(n, a@, b@)
    {
        let mut max_diff: i32 = 0;
        let mut i: usize = 0;
        let mut possible = true;
        
        while i < n
            invariant
                0 <= i && i <= n,
                a.len() == n,
                b.len() == n,
                forall|k: int| 0 <= k && k < n ==> 0 <= a@[k] && a@[k] <= 1000000000,
                forall|k: int| 0 <= k && k < n ==> 0 <= b@[k] && b@[k] <= 1000000000,
                0 <= max_diff && max_diff <= 1000000000,
                possible <==> (forall|k: int| 0 <= k && k < i ==> a@[k] >= b@[k]),
                possible ==> forall|k: int| 0 <= k && k < i ==> a@[k] - b@[k] <= max_diff,
                possible ==> (max_diff == 0 || exists|k: int| 0 <= k && k < i && a@[k] - b@[k] == max_diff),
                !possible ==> !has_valid_decrements(n, a@, b@)
            decreases n - i
        {
            if a[i] < b[i] {
                possible = false;
                proof {
                    if has_valid_decrements(n, a@, b@) {
                        let m = choose|m: i32| m >= 0 && is_valid_decrements(n, a@, b@, m);
                        assert(a@[i as int] >= b@[i as int]); 
                    }
                }
            } else {
                let diff = a[i] - b[i];
                if diff > max_diff {
                    max_diff = diff;
                }
            }
            i += 1;
        }
        
        if !possible {
            return false;
        }
        
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j && j <= n,
                a.len() == n,
                b.len() == n,
                forall|k: int| 0 <= k && k < n ==> 0 <= a@[k] && a@[k] <= 1000000000,
                forall|k: int| 0 <= k && k < n ==> 0 <= b@[k] && b@[k] <= 1000000000,
                0 <= max_diff && max_diff <= 1000000000,
                forall|k: int| 0 <= k && k < n ==> a@[k] >= b@[k],
                forall|k: int| 0 <= k && k < n ==> a@[k] - b@[k] <= max_diff,
                max_diff == 0 || exists|k: int| 0 <= k && k < n && a@[k] - b@[k] == max_diff,
                possible ==> forall|k: int| 0 <= k && k < j ==> (a@[k] - b@[k] == max_diff || b@[k] == 0),
                !possible ==> !has_valid_decrements(n, a@, b@)
            decreases n - j
        {
            let diff = a[j] - b[j];
            if diff < max_diff && b[j] != 0 {
                possible = false;
                proof {
                    if has_valid_decrements(n, a@, b@) {
                        let m = choose|m: i32| m >= 0 && is_valid_decrements(n, a@, b@, m);
                        if max_diff > 0 {
                            let k = choose|k: int| 0 <= k && k < n && a@[k] - b@[k] == max_diff;
                            assert(a@[k] - b@[k] <= m);
                        }
                        assert(m >= max_diff);
                        assert(a@[j as int] - b@[j as int] == m || b@[j as int] == 0);
                    }
                }
            }
            j += 1;
        }
        
        if possible {
            proof {
                assert(is_valid_decrements(n, a@, b@, max_diff));
            }
        }
        
        possible
    }
}
}
