use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_step_at(s: Seq<i32>, i: int) -> i32 {
    if !(0 <= i < s.len()) {
        0
    } else if i + 1 < s.len() && s[i] == 1 && s[i + 1] == 0 {
        0
    } else if i > 0 && s[i - 1] == 1 && s[i] == 0 {
        1
    } else {
        s[i]
    }
}

pub open spec fn spec_step_seq(s: Seq<i32>) -> Seq<i32> {
    Seq::new(s.len(), |i: int| spec_step_at(s, i))
}

pub open spec fn spec_after_seconds(s: Seq<i32>, t: int) -> Seq<i32>
    decreases t,
{
    if t <= 0 {
        s
    } else {
        spec_after_seconds(spec_step_seq(s), t - 1)
    }
}

impl Solution {
    pub fn queue_after_seconds(queue: Vec<i32>, t: u32) -> (result: Vec<i32>)
        requires
            1 <= queue.len() <= 50,
            t <= 50,
            forall|i: int| 0 <= i < queue.len() ==> #[trigger] queue[i] == 0 || queue[i] == 1,
        ensures
            result.len() == queue.len(),
            result@ == spec_after_seconds(queue@, t as int),
    {
    }
}

}
