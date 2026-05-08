use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

pub open spec fn spec_min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

impl Solution {
    pub fn restore_array(n: usize, b: Vec<i64>) -> (result: Vec<i64>)
        requires
            n >= 2,
            b.len() == n - 1,
            forall|i: int| 0 <= i < n - 1 ==> 0 <= #[trigger] b[i] <= 1_000_000_000,
            forall|i: int| 1 <= i < n as int - 2 ==> #[trigger] b[i] <= b[i - 1] || b[i] <= b[i + 1],
        ensures
            result.len() == n,
            forall|i: int| 0 <= i < n as int ==> #[trigger] result[i] >= 0,
            forall|i: int|
                0 <= i < n - 1 ==> spec_max(
                    #[trigger] result[i] as int,
                    result[i + 1] as int,
                ) == b[i] as int,
    {
        let mut a: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n >= 2,
                b.len() == n - 1,
                a.len() == i,
                forall|k: int| 0 <= k < n as int - 1 ==> 0 <= #[trigger] b[k] <= 1_000_000_000,
                forall|k: int| 1 <= k < n as int - 2 ==> #[trigger] b[k] <= b[k - 1] || b[k] <= b[k + 1],
                i > 0 ==> a[0] == b[0],
                forall|j: int| 1 <= j < i as int && j < n as int - 1 ==>
                    (#[trigger] a[j]) as int == spec_min(b[j - 1] as int, b[j] as int),
                forall|j: int| 0 <= j < i as int ==> 0 <= #[trigger] a[j] <= 1_000_000_000,
                forall|j: int|
                    0 <= j < i as int - 1 ==> spec_max(
                        #[trigger] a[j] as int,
                        a[j + 1] as int,
                    ) == b[j] as int,
            decreases n - i,
        {
            if i == 0 {
                a.push(b[0]);
            } else if i < n - 1 {
                if b[i - 1] <= b[i] {
                    a.push(b[i - 1]);
                } else {
                    a.push(b[i]);
                }
                proof {
                    assert(a[i as int] as int == spec_min(b[i as int - 1] as int, b[i as int] as int));
                    let j = i as int - 1;
                    if j == 0 {
                        assert(a[0] as int == b[0] as int);
                        assert(a[1] as int <= b[0] as int);
                    } else {
                        assert(a[j] as int == spec_min(b[j - 1] as int, b[j] as int));
                        assert(a[j + 1] as int == spec_min(b[j] as int, b[j + 1] as int));
                        assert(a[j] as int <= b[j] as int);
                        assert(a[j + 1] as int <= b[j] as int);
                        assert(b[j] <= b[j - 1] || b[j] <= b[j + 1]);
                        if b[j] as int <= b[j - 1] as int {
                            assert(spec_min(b[j - 1] as int, b[j] as int) == b[j] as int);
                        } else {
                            assert(b[j] as int <= b[j + 1] as int);
                            assert(spec_min(b[j] as int, b[j + 1] as int) == b[j] as int);
                        }
                    }
                    assert forall|k: int| 0 <= k < i as int implies
                        spec_max(#[trigger] a[k] as int, a[k + 1] as int) == b[k] as int by {
                        if k < i as int - 1 {
                        } else {
                        }
                    };
                    assert forall|k: int| 1 <= k < i as int + 1 && k < n as int - 1 implies
                        (#[trigger] a[k]) as int == spec_min(b[k - 1] as int, b[k] as int) by {
                        if k < i as int {
                        } else {
                        }
                    };
                    assert forall|k: int| 0 <= k < i as int + 1 implies
                        0 <= #[trigger] a[k] <= 1_000_000_000 by {
                        if k < i as int {
                        } else {
                        }
                    };
                }
            } else {
                a.push(b[n - 2]);
                proof {
                    let j = i as int - 1;
                    assert(a[i as int] as int == b[n as int - 2] as int);
                    assert(a[j + 1] as int == b[j] as int);
                    if j == 0 {
                        assert(a[0] as int == b[0] as int);
                    } else {
                        assert(a[j] as int == spec_min(b[j - 1] as int, b[j] as int));
                        assert(a[j] as int <= b[j] as int);
                    }
                    assert forall|k: int| 0 <= k < i as int implies
                        spec_max(#[trigger] a[k] as int, a[k + 1] as int) == b[k] as int by {
                        if k < i as int - 1 {
                        } else {
                        }
                    };
                    assert forall|k: int| 0 <= k < i as int + 1 implies
                        0 <= #[trigger] a[k] <= 1_000_000_000 by {
                        if k < i as int {
                        } else {
                            assert(a[k] == b[n as int - 2]);
                        }
                    };
                }
            }
            i = i + 1;
        }
        a
    }
}

}
