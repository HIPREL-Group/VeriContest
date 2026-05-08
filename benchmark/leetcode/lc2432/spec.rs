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
    }
}

}
