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
        let mut best = tasks[0][0] + tasks[0][1];
        let mut i: usize = 1;
        while i < n {
            let cur = tasks[i][0] + tasks[i][1];
            if cur < best {
                best = cur;
            }
            i = i + 1;
        }
        best
    }
}

}
