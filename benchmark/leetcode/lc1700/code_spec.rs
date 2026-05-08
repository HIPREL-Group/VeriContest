use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn simulate(queue: Seq<i32>, stack: Seq<i32>, skipped: nat) -> int
        decreases queue.len() + stack.len(), queue.len() - skipped,
    {
        if stack.len() == 0 || queue.len() == 0 {
            0
        } else if skipped >= queue.len() {
            queue.len() as int
        } else if queue[0] == stack[0] {
            Self::simulate(
                queue.subrange(1, queue.len() as int),
                stack.subrange(1, stack.len() as int),
                0,
            )
        } else {
            Self::simulate(
                queue.subrange(1, queue.len() as int) + seq![queue[0]],
                stack,
                (skipped + 1) as nat,
            )
        }
    }

    pub fn count_students(students: Vec<i32>, sandwiches: Vec<i32>) -> (result: i32)
        requires
            students.len() == sandwiches.len(),
            1 <= students.len() <= 100,
            forall|i: int| 0 <= i < students.len() ==> students[i] == 0 || students[i] == 1,
            forall|i: int| 0 <= i < sandwiches.len() ==> sandwiches[i] == 0 || sandwiches[i] == 1,
        ensures
            result as int == Self::simulate(students@, sandwiches@, 0),
    {
        let mut queue: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < students.len() {
            queue.push(students[idx]);
            idx = idx + 1;
        }
        let mut sand_idx: usize = 0;
        let mut skipped: usize = 0;
        while sand_idx < sandwiches.len() && skipped < queue.len() {
            if queue[0] == sandwiches[sand_idx] {
                let mut new_queue: Vec<i32> = Vec::new();
                let mut k: usize = 1;
                while k < queue.len() {
                    new_queue.push(queue[k]);
                    k = k + 1;
                }
                queue = new_queue;
                sand_idx = sand_idx + 1;
                skipped = 0;
            } else {
                let front: i32 = queue[0];
                let mut new_queue: Vec<i32> = Vec::new();
                let mut k: usize = 1;
                while k < queue.len() {
                    new_queue.push(queue[k]);
                    k = k + 1;
                }
                new_queue.push(front);
                queue = new_queue;
                skipped = skipped + 1;
            }
        }
        queue.len() as i32
    }
}

}
