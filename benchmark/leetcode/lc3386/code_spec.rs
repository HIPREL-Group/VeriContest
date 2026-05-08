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
        let n = events.len();
        let mut best_idx: i32 = events[0][0];
        let mut best_time: i32 = events[0][1];
        let mut prev_time: i32 = events[0][1];
        let mut i: usize = 1;
        while i < n {
            let current_idx: i32 = events[i][0];
            let current_time: i32 = events[i][1] - prev_time;
            if current_time > best_time {
                best_time = current_time;
                best_idx = current_idx;
            } else if current_time == best_time && current_idx < best_idx {
                best_idx = current_idx;
            }
            prev_time = events[i][1];
            i = i + 1;
        }
        best_idx
    }
}

}
