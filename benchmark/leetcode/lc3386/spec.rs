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
    }
}

}
