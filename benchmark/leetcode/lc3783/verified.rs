use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn reverse_checked_spec_helper(x: nat, acc: nat) -> int
        decreases x,
    {
        if x == 0 {
            acc as int
        } else {
            let next = acc * 10 + x % 10;
            if next > i32::MAX as nat {
                -1
            } else {
                Solution::reverse_checked_spec_helper(x / 10, next)
            }
        }
    }

    pub open spec fn reverse_checked_spec(x: nat) -> int {
        Solution::reverse_checked_spec_helper(x, 0)
    }

    pub open spec fn mirror_distance_spec(n: int) -> int {
        let r = Solution::reverse_checked_spec(n as nat);
        if r == -1 {
            n
        } else if n >= r {
            n - r
        } else {
            r - n
        }
    }

    pub fn mirror_distance(n: i32) -> (res: i32)
        requires
            1 <= n <= 1_000_000_000,
        ensures
            res as int == Solution::mirror_distance_spec(n as int),
    {
        let mut cur: i32 = n;
        let mut rev: i32 = 0;

        while cur > 0
            invariant
                0 <= cur <= n,
                0 <= rev <= i32::MAX,
                Solution::reverse_checked_spec_helper(cur as nat, rev as nat)
                    == Solution::reverse_checked_spec(n as nat),
            decreases cur,
        {
            let old_cur = cur;
            let old_rev = rev;
            let digit: i32 = cur % 10;
            match rev.checked_mul(10) {
                None => {
                    proof {
                        assert(old_cur > 0);
                        assert(old_rev as int * 10 > i32::MAX);
                        assert(old_rev as int * 10 + old_cur as int % 10 > i32::MAX);
                        assert(
                            Solution::reverse_checked_spec_helper(old_cur as nat, old_rev as nat) == -1
                        );
                        assert(
                            Solution::reverse_checked_spec(n as nat)
                                == Solution::reverse_checked_spec_helper(old_cur as nat, old_rev as nat)
                        );
                        assert(Solution::reverse_checked_spec(n as nat) == -1);
                        assert(Solution::mirror_distance_spec(n as int) == n as int);
                    }
                    return n;
                }
                Some(tmp) => {
                    match tmp.checked_add(digit) {
                        None => {
                            proof {
                                assert(old_cur > 0);
                                assert(tmp as int == old_rev as int * 10);
                                assert(digit as int == old_cur as int % 10);
                                assert(tmp as int + digit as int > i32::MAX);
                                assert(old_rev as int * 10 + old_cur as int % 10 > i32::MAX);
                                assert(
                                    Solution::reverse_checked_spec_helper(old_cur as nat, old_rev as nat)
                                        == -1
                                );
                                assert(
                                    Solution::reverse_checked_spec(n as nat)
                                        == Solution::reverse_checked_spec_helper(old_cur as nat, old_rev as nat)
                                );
                                assert(Solution::reverse_checked_spec(n as nat) == -1);
                                assert(Solution::mirror_distance_spec(n as int) == n as int);
                            }
                            return n;
                        }
                        Some(next) => {
                            proof {
                                assert(old_cur > 0);
                                assert(tmp as int == old_rev as int * 10);
                                assert(digit as int == old_cur as int % 10);
                                assert(next as int == tmp as int + digit as int);
                                assert(next as int == old_rev as int * 10 + old_cur as int % 10);
                                assert(next as int <= i32::MAX);
                                assert(next as nat == old_rev as nat * 10 + old_cur as nat % 10);
                                assert(
                                    Solution::reverse_checked_spec_helper(old_cur as nat, old_rev as nat)
                                        == Solution::reverse_checked_spec_helper(
                                        (old_cur / 10) as nat,
                                        next as nat,
                                    )
                                );
                            }
                            rev = next;
                        }
                    }
                }
            }
            cur = cur / 10;
        }

        proof {
            assert(cur == 0);
            assert(
                Solution::reverse_checked_spec_helper(cur as nat, rev as nat)
                    == Solution::reverse_checked_spec(n as nat)
            );
            assert(Solution::reverse_checked_spec_helper(0nat, rev as nat) == rev as int);
            assert(Solution::reverse_checked_spec(n as nat) == rev as int);
        }

        if n >= rev {
            proof {
                assert(n as int >= rev as int);
                assert(Solution::reverse_checked_spec(n as nat) == rev as int);
                assert(Solution::mirror_distance_spec(n as int) == n as int - rev as int);
            }
            n - rev
        } else {
            proof {
                assert(rev as int > n as int);
                assert(Solution::reverse_checked_spec(n as nat) == rev as int);
                assert(Solution::mirror_distance_spec(n as int) == rev as int - n as int);
            }
            rev - n
        }
    }
}

} 
