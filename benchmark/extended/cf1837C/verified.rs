use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn best_binary_string(s: Vec<i64>) -> (result: Vec<i64>)
        requires
            s.len() >= 1,
            forall|i: int| 0 <= i < s.len() ==> (#[trigger] s@[i] == 0 || s@[i] == 1 || s@[i] == 2),
        ensures
            result@.len() == s@.len(),
            forall|i: int| 0 <= i < result@.len() ==> (#[trigger] result@[i] == 0 || result@[i] == 1),
            forall|i: int| 0 <= i < s@.len() && s@[i] != 2 ==> #[trigger] result@[i] == s@[i],
            forall|i: int| 0 <= i < s@.len() && s@[i] == 2 ==>
                #[trigger] result@[i] == if i == 0 { 0 } else { result@[i - 1] },
    {
        let n = s.len();
        let mut result: Vec<i64> = Vec::new();
        let mut last: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == s.len(),
                i <= n,
                result.len() == i,
                last == 0 || last == 1,
                i == 0 ==> last == 0,
                forall|k: int| 0 <= k < s.len() ==> (#[trigger] s@[k] == 0 || s@[k] == 1 || s@[k] == 2),
                i > 0 ==> last == result@[i as int - 1],
                forall|k: int| 0 <= k < i as int ==> (#[trigger] result@[k] == 0 || result@[k] == 1),
                forall|k: int| 0 <= k < i as int && s@[k] != 2 ==> #[trigger] result@[k] == s@[k],
                forall|k: int| 0 <= k < i as int && s@[k] == 2 ==>
                    #[trigger] result@[k] == if k == 0 { 0 } else { result@[k - 1] },
            decreases n - i,
        {
            let ghost old_result = result@;
            let i0: usize = i;
            let old_last: i64 = last;
            if s[i] != 2 {
                last = s[i];
            }
            result.push(last);
            i = i + 1;
            proof {
                assert(i == i0 + 1);
                assert(result@ == old_result.push(last));
                assert forall|k: int| 0 <= k < i as int implies
                    (#[trigger] result@[k] == 0 || result@[k] == 1)
                by {
                    if k < i as int - 1 {
                        assert(result@[k] == old_result[k]);
                    }
                }
                assert forall|k: int| (0 <= k < i as int && s@[k] != 2) implies
                    #[trigger] result@[k] == s@[k]
                by {
                    if k < i as int - 1 {
                        assert(result@[k] == old_result[k]);
                    }
                }
                assert forall|k: int| (0 <= k < i as int && s@[k] == 2) implies
                    #[trigger] result@[k] == if k == 0 { 0 } else { result@[k - 1] }
                by {
                    if k < i as int - 1 {
                        assert(result@[k] == old_result[k]);
                        if k > 0 {
                            assert(result@[k - 1] == old_result[k - 1]);
                        }
                    } else {
                        if k == 0 {
                            assert(i as int - 1 == k);
                            assert(i as int == 1);
                            assert(i0 == 0);
                            assert(s@[k] == 2);
                            assert(s@[i0 as int] == 2);
                            assert(s[i0 as int] == 2);
                            assert(last == old_last);
                            assert(old_last == 0);
                            assert(result@[k] == last);
                        } else {
                            assert(result@[k - 1] == old_result[k - 1]);
                        }
                    }
                }
            }
        }
        result
    }
}

}
