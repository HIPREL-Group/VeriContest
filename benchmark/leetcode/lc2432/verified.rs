use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn task_duration(logs: Seq<Vec<i32>>, idx: int) -> int
        recommends
            0 <= idx < logs.len(),
            forall |k: int| 0 <= k < logs.len() ==> logs[k].len() == 2,
    {
        if idx == 0 {
            logs[0][1] as int
        } else {
            logs[idx][1] as int - logs[idx - 1][1] as int
        }
    }

    pub open spec fn best_dur_prefix(logs: Seq<Vec<i32>>, len: int) -> int
        recommends
            1 <= len <= logs.len(),
            forall |k: int| 0 <= k < logs.len() ==> logs[k].len() == 2,
        decreases len,
    {
        if len <= 1 {
            logs[0][1] as int
        } else {
            let prev = Self::best_dur_prefix(logs, len - 1);
            let cur = Self::task_duration(logs, len - 1);
            if cur > prev { cur } else { prev }
        }
    }

    pub open spec fn best_id_prefix(logs: Seq<Vec<i32>>, len: int) -> int
        recommends
            1 <= len <= logs.len(),
            forall |k: int| 0 <= k < logs.len() ==> logs[k].len() == 2,
        decreases len,
    {
        if len <= 1 {
            logs[0][0] as int
        } else {
            let prev_id = Self::best_id_prefix(logs, len - 1);
            let prev_dur = Self::best_dur_prefix(logs, len - 1);
            let cur_dur = Self::task_duration(logs, len - 1);
            let cur_id = logs[len - 1][0] as int;
            if cur_dur > prev_dur {
                cur_id
            } else if cur_dur < prev_dur {
                prev_id
            } else if cur_id < prev_id {
                cur_id
            } else {
                prev_id
            }
        }
    }

    pub fn hardest_worker(n: i32, logs: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= n <= 500,
            1 <= logs.len() <= 500,
            forall |i: int| 0 <= i < logs.len() ==> logs[i].len() == 2,
            forall |i: int| 0 <= i < logs.len() ==> 0 <= #[trigger] logs[i][0] < n,
            forall |i: int| 0 <= i < logs.len() ==> 1 <= #[trigger] logs[i][1] <= 500,
            forall |i: int| 1 <= i < logs.len() ==> logs[i - 1][1] < #[trigger] logs[i][1],
        ensures
            result as int == Self::best_id_prefix(logs@, logs.len() as int),
    {
        let mut best_id: i32 = logs[0][0];
        let mut best_dur: i32 = logs[0][1];
        let mut prev: i32 = logs[0][1];
        let mut i: usize = 1;

        while i < logs.len()
            invariant
                1 <= i <= logs.len(),
                forall |k: int| 0 <= k < logs.len() ==> #[trigger] logs[k].len() == 2,
                forall |k: int| 0 <= k < logs.len() ==> 1 <= #[trigger] logs[k][1] <= 500,
                forall |k: int| 1 <= k < logs.len() ==> logs[k - 1][1] < #[trigger] logs[k][1],
                prev == logs[i - 1][1],
                1 <= prev <= 500,
                best_dur as int == Self::best_dur_prefix(logs@, i as int),
                best_id as int == Self::best_id_prefix(logs@, i as int),
            decreases logs.len() - i,
        {
            proof {
                assert(0 <= (i as int) < (logs.len() as int));
                assert(logs[i as int].len() == 2);
                assert(1 <= logs[i as int][1] <= 500);
            }
            let id: i32 = logs[i][0];
            let cur: i32 = logs[i][1];
            proof {
                assert(1 <= prev <= 500);
                assert(1 <= cur <= 500);
                assert(1 <= (i as int) < (logs.len() as int));
                assert(logs[i as int - 1][1] < logs[i as int][1]);
                assert(prev < cur);
                assert(-2_147_483_648 <= cur - prev < 2_147_483_647);
            }
            let dur: i32 = cur - prev;

            if dur > best_dur || (dur == best_dur && id < best_id) {
                best_dur = dur;
                best_id = id;
            }

            proof {
                let ghost old_dur = Self::best_dur_prefix(logs@, i as int);
                let ghost old_id = Self::best_id_prefix(logs@, i as int);
                let ghost cur_dur_s = Self::task_duration(logs@, i as int);
                let ghost cur_id_s = logs[i as int][0] as int;
                assert(dur as int == cur_dur_s);
                assert(id as int == cur_id_s);
                assert(best_dur as int == if cur_dur_s > old_dur { cur_dur_s } else { old_dur });
                if cur_dur_s > old_dur {
                    assert(best_id as int == cur_id_s);
                } else if cur_dur_s < old_dur {
                    assert(best_id as int == old_id);
                } else if cur_id_s < old_id {
                    assert(best_id as int == cur_id_s);
                } else {
                    assert(best_id as int == old_id);
                }
                assert(best_dur as int == Self::best_dur_prefix(logs@, i as int + 1));
                assert(best_id as int == Self::best_id_prefix(logs@, i as int + 1));
            }

            prev = cur;
            i = i + 1;
        }

        best_id
    }
}

}
