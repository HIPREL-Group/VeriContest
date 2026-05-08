use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_event(e: Seq<i32>) -> bool {
        e.len() == 2 && 1 <= e[0] <= 100000 && 1 <= e[1] <= 100000
    }

    pub open spec fn press_time(events: Seq<Vec<i32>>, i: int) -> int
        recommends
            0 <= i < events.len(),
            forall |k: int| 0 <= k < events.len() ==> Self::valid_event(events[k]@),
    {
        if i == 0 {
            events[0][1] as int
        } else {
            events[i][1] as int - events[i - 1][1] as int
        }
    }

    pub fn button_with_longest_time(events: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= events.len() <= 1000,
            forall |i: int| 0 <= i < events.len() ==> Self::valid_event(events[i]@),
            forall |i: int, j: int|
                0 <= i < j < events.len()
                && Self::valid_event(events[i]@)
                && Self::valid_event(events[j]@)
                ==> events[i][1] <= events[j][1],
        ensures
            exists |best_pos: int|
                0 <= best_pos < events.len()
                && Self::valid_event(events[best_pos]@)
                && result == events[best_pos][0]
                && forall |j: int|
                    0 <= j < events.len() && Self::valid_event(events[j]@)
                    ==> Self::press_time(events@, j) < Self::press_time(events@, best_pos)
                        || (Self::press_time(events@, j) == Self::press_time(events@, best_pos)
                            && result <= events[j][0]),
    {
        proof {
            assert(events.len() >= 1);
            assert(Self::valid_event(events[0]@));
        }

        let n = events.len();
        let mut best_idx: i32 = events[0][0];
        let mut best_time: i32 = events[0][1];
        let mut prev_time: i32 = events[0][1];
        let ghost mut best_pos: int = 0;

        proof {
            assert(best_time as int == Self::press_time(events@, 0));
            assert(best_idx == events[0][0]);
            assert forall |k: int| 0 <= k < 1 && Self::valid_event(events[k]@) implies
                Self::press_time(events@, k) < best_time as int
                || (Self::press_time(events@, k) == best_time as int && best_idx <= events[k][0]) by {
                assert(k == 0);
            };
        }

        let mut i: usize = 1;
        while i < n
            invariant
                n == events.len(),
                1 <= n <= 1000,
                forall |k: int| 0 <= k < events.len() ==> Self::valid_event(events[k]@),
                1 <= i <= n,
                prev_time == events[i - 1][1],
                0 <= best_pos < i as int,
                best_idx == events[best_pos][0],
                best_time as int == Self::press_time(events@, best_pos),
                forall |k: int|
                    0 <= k < i as int && Self::valid_event(events[k]@)
                    ==> Self::press_time(events@, k) < best_time as int
                        || (Self::press_time(events@, k) == best_time as int
                            && best_idx <= events[k][0]),
            decreases n - i,
        {
            proof {
                assert(Self::valid_event(events[i as int]@));
                assert(Self::valid_event(events[i as int - 1]@));
            }

            let current_idx: i32 = events[i][0];
            let current_time: i32 = events[i][1] - prev_time;

            proof {
                assert(prev_time == events[i as int - 1][1]);
                assert(current_time as int == events[i as int][1] as int - events[i as int - 1][1] as int);
                assert(current_time as int == Self::press_time(events@, i as int));
            }

            let ghost old_best_pos = best_pos;
            let ghost old_best_idx = best_idx;
            let ghost old_best_time = best_time as int;

            if current_time > best_time {
                best_time = current_time;
                best_idx = current_idx;
                proof {
                    best_pos = i as int;
                }
                proof {
                    assert(best_time as int == Self::press_time(events@, best_pos));
                    assert(best_idx == events[best_pos][0]);
                    assert forall |k: int| 0 <= k < i as int + 1 && Self::valid_event(events[k]@) implies
                        Self::press_time(events@, k) < best_time as int
                        || (Self::press_time(events@, k) == best_time as int
                            && best_idx <= events[k][0]) by {
                        if k < i as int {
                            assert(Self::press_time(events@, k) < old_best_time
                                || (Self::press_time(events@, k) == old_best_time
                                    && old_best_idx <= events[k][0]));
                            if Self::press_time(events@, k) == old_best_time {
                                assert(Self::press_time(events@, k) < best_time as int);
                            }
                            if Self::press_time(events@, k) < old_best_time {
                                assert(Self::press_time(events@, k) < best_time as int);
                            }
                        } else {
                            assert(k == i as int);
                            assert(Self::press_time(events@, k) == best_time as int);
                            assert(best_idx == events[k][0]);
                        }
                    };
                }
            } else if current_time == best_time && current_idx < best_idx {
                best_idx = current_idx;
                proof {
                    best_pos = i as int;
                }
                proof {
                    assert(best_time as int == old_best_time);
                    assert(best_time as int == Self::press_time(events@, best_pos));
                    assert(best_idx == events[best_pos][0]);
                    assert forall |k: int| 0 <= k < i as int + 1 && Self::valid_event(events[k]@) implies
                        Self::press_time(events@, k) < best_time as int
                        || (Self::press_time(events@, k) == best_time as int
                            && best_idx <= events[k][0]) by {
                        if k < i as int {
                            assert(Self::press_time(events@, k) < old_best_time
                                || (Self::press_time(events@, k) == old_best_time
                                    && old_best_idx <= events[k][0]));
                            if Self::press_time(events@, k) == old_best_time {
                                assert(best_idx < old_best_idx);
                                assert(best_idx <= events[k][0]);
                            }
                        } else {
                            assert(k == i as int);
                            assert(Self::press_time(events@, k) == best_time as int);
                            assert(best_idx == events[k][0]);
                        }
                    };
                }
            } else {
                proof {
                    assert(best_pos == old_best_pos);
                    assert(best_time as int == old_best_time);
                    assert(best_idx == old_best_idx);
                    assert forall |k: int| 0 <= k < i as int + 1 && Self::valid_event(events[k]@) implies
                        Self::press_time(events@, k) < best_time as int
                        || (Self::press_time(events@, k) == best_time as int
                            && best_idx <= events[k][0]) by {
                        if k < i as int {
                            assert(Self::press_time(events@, k) < old_best_time
                                || (Self::press_time(events@, k) == old_best_time
                                    && old_best_idx <= events[k][0]));
                        } else {
                            assert(k == i as int);
                            assert(Self::press_time(events@, k) == current_time as int);
                            assert(current_time as int <= best_time as int);
                            if Self::press_time(events@, k) == best_time as int {
                                assert(current_time == best_time);
                                assert(!(current_idx < best_idx));
                                assert(best_idx <= events[k][0]);
                            }
                        }
                    };
                }
            }

            prev_time = events[i][1];
            i = i + 1;
        }

        proof {
            assert(i == n);
            assert(exists |p: int|
                0 <= p < events.len()
                && Self::valid_event(events[p]@)
                && best_idx == events[p][0]
                && forall |j: int|
                    0 <= j < events.len() && Self::valid_event(events[j]@)
                    ==> Self::press_time(events@, j) < Self::press_time(events@, p)
                        || (Self::press_time(events@, j) == Self::press_time(events@, p)
                            && best_idx <= events[j][0])) by {
                let p = best_pos;
                assert(0 <= p < events.len());
                assert(Self::valid_event(events[p]@));
                assert(best_idx == events[p][0]);
                assert forall |j: int|
                    0 <= j < events.len() && Self::valid_event(events[j]@)
                    implies Self::press_time(events@, j) < Self::press_time(events@, p)
                        || (Self::press_time(events@, j) == Self::press_time(events@, p)
                            && best_idx <= events[j][0]) by {
                    assert(j < i as int);
                    assert(Self::press_time(events@, j) < best_time as int
                        || (Self::press_time(events@, j) == best_time as int
                            && best_idx <= events[j][0]));
                    assert(Self::press_time(events@, p) == best_time as int);
                };
            };
        }

        best_idx
    }
}

}
