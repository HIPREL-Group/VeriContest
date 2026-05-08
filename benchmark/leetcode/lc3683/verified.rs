use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_task(task: Seq<i32>) -> bool {
        task.len() == 2 && 1 <= task[0] <= 100 && 1 <= task[1] <= 100
    }

    pub open spec fn finish_time(tasks: Seq<Vec<i32>>, i: int) -> int
        recommends
            0 <= i < tasks.len(),
            forall |k: int| 0 <= k < tasks.len() ==> Self::valid_task(tasks[k]@),
    {
        tasks[i][0] as int + tasks[i][1] as int
    }

    pub fn earliest_time(tasks: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= tasks.len() <= 100,
            forall |i: int| 0 <= i < tasks.len() ==> #[trigger] Self::valid_task(tasks[i]@),
        ensures
            exists |j: int|
                0 <= j < tasks.len()
                && result as int == Self::finish_time(tasks@, j)
                && forall |k: int| 0 <= k < tasks.len() ==> result as int <= #[trigger] Self::finish_time(tasks@, k),
    {
        let n = tasks.len();

        proof {
            assert(Self::valid_task(tasks[0]@));
            assert(1 <= tasks[0][0] <= 100);
            assert(1 <= tasks[0][1] <= 100);
            assert(2 <= tasks[0][0] + tasks[0][1] <= 200);
            assert(tasks[0][0] + tasks[0][1] == Self::finish_time(tasks@, 0));
        }

        let mut best = tasks[0][0] + tasks[0][1];
        let mut i: usize = 1;
        let ghost mut best_idx: int = 0;

        while i < n
            invariant
                n == tasks.len(),
                1 <= n <= 100,
                1 <= i <= n,
                forall |t: int| 0 <= t < tasks.len() ==> #[trigger] Self::valid_task(tasks[t]@),
                0 <= best_idx < i as int,
                best as int == Self::finish_time(tasks@, best_idx),
                forall |k: int| 0 <= k < i as int ==> best as int <= #[trigger] Self::finish_time(tasks@, k),
                2 <= best <= 200,
            decreases n - i,
        {
            proof {
                assert(Self::valid_task(tasks[i as int]@));
                assert(1 <= tasks[i as int][0] <= 100);
                assert(1 <= tasks[i as int][1] <= 100);
                assert(2 <= tasks[i as int][0] + tasks[i as int][1] <= 200);
            }

            let cur = tasks[i][0] + tasks[i][1];
            let old_best = best;
            let ghost old_i = i as int;
            let ghost old_best_idx = best_idx;

            proof {
                assert(cur as int == Self::finish_time(tasks@, old_i));
            }

            if cur < best {
                best = cur;
                proof {
                    best_idx = old_i;
                }
            }

            proof {
                if cur < old_best {
                    assert(best == cur);
                    assert(best_idx == old_i);
                } else {
                    assert(best == old_best);
                    assert(best_idx == old_best_idx);
                }

                assert forall |k: int| 0 <= k < old_i + 1 implies best as int <= #[trigger] Self::finish_time(tasks@, k) by {
                    if k < old_i {
                        assert(old_best as int <= Self::finish_time(tasks@, k));
                        if cur < old_best {
                            assert(best as int == cur as int);
                            assert((cur as int) < (old_best as int));
                            assert(best as int <= Self::finish_time(tasks@, k));
                        } else {
                            assert(best as int == old_best as int);
                        }
                    } else {
                        assert(k == old_i);
                        assert(cur as int == Self::finish_time(tasks@, k));
                        if cur < old_best {
                            assert(best as int == cur as int);
                        } else {
                            assert(best as int == old_best as int);
                            assert(!((cur as int) < (old_best as int)));
                            assert((old_best as int) <= (cur as int));
                        }
                        assert(best as int <= Self::finish_time(tasks@, k));
                    }
                };

                assert(2 <= best <= 200);
            }

            i = i + 1;
        }

        proof {
            assert(i == n);
            assert(0 <= best_idx < tasks.len());
            assert(best as int == Self::finish_time(tasks@, best_idx));
            assert forall |k: int| 0 <= k < tasks.len() implies best as int <= #[trigger] Self::finish_time(tasks@, k) by {
                assert(k < i as int);
            };
            assert(exists |j: int|
                0 <= j < tasks.len()
                && best as int == Self::finish_time(tasks@, j)
                && forall |k: int| 0 <= k < tasks.len() ==> best as int <= #[trigger] Self::finish_time(tasks@, k));
        }

        best
    }
}

}
