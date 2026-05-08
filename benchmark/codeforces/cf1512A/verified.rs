use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_spy(a: Seq<i64>, i: int) -> bool {
    &&& 0 <= i < a.len()
    &&& forall|j: int| 0 <= j < a.len() && j != i ==> a[j] != a[i]
    &&& forall|j: int, k: int| 0 <= j < a.len() && 0 <= k < a.len() && j != i && k != i ==> a[j] == a[k]
}

impl Solution {
    pub fn spy_index(a: Vec<i64>) -> (res: usize)
        requires
            3 <= a.len() <= 100,
            exists|i: int| is_spy(a@, i),
        ensures
            is_spy(a@, res as int - 1),
    {
        let n = a.len();
        let ghost spy: int = choose|i: int| is_spy(a@, i);

        if a[0] != a[1] {
            if a[0] == a[2] {
                proof {
                    assert(spy == 1) by {
                        if spy != 1 {
                            if spy == 0 {
                                assert(a@[1] == a@[2]);
                            } else if spy == 2 {
                                assert(a@[0] == a@[1]);
                            } else {
                                assert(0 <= spy < a@.len());
                                assert(a@[0] == a@[1]);
                            }
                        }
                    }
                    assert(is_spy(a@, 1));
                }
                return 2;
            } else {
                proof {
                    assert(spy == 0) by {
                        if spy != 0 {
                            if spy == 1 {
                                assert(a@[0] == a@[2]);
                            } else if spy == 2 {
                                assert(a@[0] == a@[1]);
                            } else {
                                assert(0 <= spy < a@.len());
                                assert(a@[0] == a@[1]);
                            }
                        }
                    }
                    assert(is_spy(a@, 0));
                }
                return 1;
            }
        }

        proof {
            assert(spy != 0) by {
                if spy == 0 {
                    assert(a@[1] != a@[0]);
                }
            }
            assert(spy != 1) by {
                if spy == 1 {
                    assert(a@[0] != a@[1]);
                }
            }
            assert(2 <= spy < a@.len());
            assert(a@[spy] != a@[0]);
        }

        let mut i: usize = 2;
        while i < n
            invariant
                n == a.len(),
                2 <= i <= n,
                is_spy(a@, spy),
                2 <= spy < n as int,
                a@[spy] != a@[0],
                forall|j: int| 2 <= j < i as int ==> (#[trigger] a@[j]) == a@[0],
            decreases n - i,
        {
            if a[i] != a[0] {
                proof {
                    assert(i as int == spy) by {
                        if i as int != spy {
                            assert(0 != spy);
                            assert(a@[i as int] == a@[0]);
                        }
                    }
                    assert(is_spy(a@, i as int));
                }
                return i + 1;
            }
            proof {
                assert(a@[i as int] == a@[0]);
            }
            i += 1;
        }

        proof {
            assert(i == n);
            assert(spy < n as int);
            assert(2 <= spy < i as int);
            assert(a@[spy] == a@[0]);
            assert(a@[spy] != a@[0]);
        }
        1
    }
}

}
