use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn merge_triplets(triplets: Vec<Vec<i32>>, target: Vec<i32>) -> (res: bool)
        requires
            1 <= triplets.len() <= 100_000,
            target.len() == 3,
            forall |i: int| 0 <= i < triplets.len() ==> #[trigger] triplets[i].len() == 3,
            forall |i: int, j: int| 0 <= i < triplets.len() && 0 <= j < triplets[i].len() ==> 1 <= #[trigger] triplets[i][j] <= 1000,
            forall |j: int| 0 <= j < 3 ==> 1 <= #[trigger] target[j] <= 1000,
        ensures
            res == (
                (exists |i: int|
                    0 <= i < triplets.len()
                    && triplets[i].len() == 3
                    && triplets[i][0] == target[0]
                    && triplets[i][1] <= target[1]
                    && triplets[i][2] <= target[2]
                )
                && (exists |i: int|
                    0 <= i < triplets.len()
                    && triplets[i].len() == 3
                    && triplets[i][0] <= target[0]
                    && triplets[i][1] == target[1]
                    && triplets[i][2] <= target[2]
                )
                && (exists |i: int|
                    0 <= i < triplets.len()
                    && triplets[i].len() == 3
                    && triplets[i][0] <= target[0]
                    && triplets[i][1] <= target[1]
                    && triplets[i][2] == target[2]
                )
            ),
    {
        let mut has0 = false;
        let mut has1 = false;
        let mut has2 = false;
        let mut i = 0usize;

        while i < triplets.len()
            invariant
                1 <= triplets.len() <= 100_000,
                target.len() == 3,
                forall |k: int| 0 <= k < triplets.len() ==> #[trigger] triplets[k].len() == 3,
                forall |k: int, j: int| 0 <= k < triplets.len() && 0 <= j < triplets[k].len() ==> 1 <= #[trigger] triplets[k][j] <= 1000,
                forall |j: int| 0 <= j < 3 ==> 1 <= #[trigger] target[j] <= 1000,
                0 <= i <= triplets.len(),
                has0 == (exists |k: int|
                    0 <= k < i
                    && triplets[k].len() == 3
                    && triplets[k][0] == target[0]
                    && triplets[k][1] <= target[1]
                    && triplets[k][2] <= target[2]
                ),
                has1 == (exists |k: int|
                    0 <= k < i
                    && triplets[k].len() == 3
                    && triplets[k][0] <= target[0]
                    && triplets[k][1] == target[1]
                    && triplets[k][2] <= target[2]
                ),
                has2 == (exists |k: int|
                    0 <= k < i
                    && triplets[k].len() == 3
                    && triplets[k][0] <= target[0]
                    && triplets[k][1] <= target[1]
                    && triplets[k][2] == target[2]
                ),
            decreases triplets.len() - i,
        {
            assert(triplets[i as int].len() == 3);
            let t0 = triplets[i][0];
            let t1 = triplets[i][1];
            let t2 = triplets[i][2];
            let ghost old_has0 = has0;
            let ghost old_has1 = has1;
            let ghost old_has2 = has2;

            has0 = has0 || (t0 == target[0] && t1 <= target[1] && t2 <= target[2]);
            has1 = has1 || (t0 <= target[0] && t1 == target[1] && t2 <= target[2]);
            has2 = has2 || (t0 <= target[0] && t1 <= target[1] && t2 == target[2]);

            proof {
                let idx = i as int;

                assert(has0 == (exists |k: int|
                    0 <= k < idx + 1
                    && triplets[k].len() == 3
                    && triplets[k][0] == target[0]
                    && triplets[k][1] <= target[1]
                    && triplets[k][2] <= target[2]
                )) by {
                    if has0 {
                        if old_has0 {
                            assert(exists |k: int|
                                0 <= k < idx
                                && triplets[k].len() == 3
                                && triplets[k][0] == target[0]
                                && triplets[k][1] <= target[1]
                                && triplets[k][2] <= target[2]
                            );
                        } else {
                            assert(t0 == target[0] && t1 <= target[1] && t2 <= target[2]);
                            assert(0 <= idx < idx + 1);
                        }
                    } else {
                        assert(!old_has0);
                        assert(!(t0 == target[0] && t1 <= target[1] && t2 <= target[2]));
                        assert forall |k: int|
                            0 <= k < idx + 1
                            && triplets[k].len() == 3
                            && triplets[k][0] == target[0]
                            && triplets[k][1] <= target[1]
                            && triplets[k][2] <= target[2]
                            implies false by {
                            if k < idx {
                                if triplets[k][0] == target[0] && triplets[k][1] <= target[1] && triplets[k][2] <= target[2] {
                                    assert(exists |m: int|
                                        0 <= m < idx
                                        && triplets[m].len() == 3
                                        && triplets[m][0] == target[0]
                                        && triplets[m][1] <= target[1]
                                        && triplets[m][2] <= target[2]
                                    );
                                    assert(old_has0);
                                }
                            } else {
                                assert(k == idx);
                                assert(triplets[k][0] == t0);
                                assert(triplets[k][1] == t1);
                                assert(triplets[k][2] == t2);
                            }
                        };
                    }
                };

                assert(has1 == (exists |k: int|
                    0 <= k < idx + 1
                    && triplets[k].len() == 3
                    && triplets[k][0] <= target[0]
                    && triplets[k][1] == target[1]
                    && triplets[k][2] <= target[2]
                )) by {
                    if has1 {
                        if old_has1 {
                            assert(exists |k: int|
                                0 <= k < idx
                                && triplets[k].len() == 3
                                && triplets[k][0] <= target[0]
                                && triplets[k][1] == target[1]
                                && triplets[k][2] <= target[2]
                            );
                        } else {
                            assert(t0 <= target[0] && t1 == target[1] && t2 <= target[2]);
                            assert(0 <= idx < idx + 1);
                        }
                    } else {
                        assert(!old_has1);
                        assert(!(t0 <= target[0] && t1 == target[1] && t2 <= target[2]));
                        assert forall |k: int|
                            0 <= k < idx + 1
                            && triplets[k].len() == 3
                            && triplets[k][0] <= target[0]
                            && triplets[k][1] == target[1]
                            && triplets[k][2] <= target[2]
                            implies false by {
                            if k < idx {
                                if triplets[k][0] <= target[0] && triplets[k][1] == target[1] && triplets[k][2] <= target[2] {
                                    assert(exists |m: int|
                                        0 <= m < idx
                                        && triplets[m].len() == 3
                                        && triplets[m][0] <= target[0]
                                        && triplets[m][1] == target[1]
                                        && triplets[m][2] <= target[2]
                                    );
                                    assert(old_has1);
                                }
                            } else {
                                assert(k == idx);
                                assert(triplets[k][0] == t0);
                                assert(triplets[k][1] == t1);
                                assert(triplets[k][2] == t2);
                            }
                        };
                    }
                };

                assert(has2 == (exists |k: int|
                    0 <= k < idx + 1
                    && triplets[k].len() == 3
                    && triplets[k][0] <= target[0]
                    && triplets[k][1] <= target[1]
                    && triplets[k][2] == target[2]
                )) by {
                    if has2 {
                        if old_has2 {
                            assert(exists |k: int|
                                0 <= k < idx
                                && triplets[k].len() == 3
                                && triplets[k][0] <= target[0]
                                && triplets[k][1] <= target[1]
                                && triplets[k][2] == target[2]
                            );
                        } else {
                            assert(t0 <= target[0] && t1 <= target[1] && t2 == target[2]);
                            assert(0 <= idx < idx + 1);
                        }
                    } else {
                        assert(!old_has2);
                        assert(!(t0 <= target[0] && t1 <= target[1] && t2 == target[2]));
                        assert forall |k: int|
                            0 <= k < idx + 1
                            && triplets[k].len() == 3
                            && triplets[k][0] <= target[0]
                            && triplets[k][1] <= target[1]
                            && triplets[k][2] == target[2]
                            implies false by {
                            if k < idx {
                                if triplets[k][0] <= target[0] && triplets[k][1] <= target[1] && triplets[k][2] == target[2] {
                                    assert(exists |m: int|
                                        0 <= m < idx
                                        && triplets[m].len() == 3
                                        && triplets[m][0] <= target[0]
                                        && triplets[m][1] <= target[1]
                                        && triplets[m][2] == target[2]
                                    );
                                    assert(old_has2);
                                }
                            } else {
                                assert(k == idx);
                                assert(triplets[k][0] == t0);
                                assert(triplets[k][1] == t1);
                                assert(triplets[k][2] == t2);
                            }
                        };
                    }
                };
            }

            i += 1;
        }

        has0 && has1 && has2
    }
}

}