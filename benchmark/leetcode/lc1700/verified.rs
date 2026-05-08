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
        while idx < students.len()
            invariant
                0 <= idx <= students.len(),
                queue@.len() == idx as int,
                forall|j: int| 0 <= j < idx as int ==> queue@[j] == students@[j],
            decreases students.len() - idx,
        {
            queue.push(students[idx]);
            idx = idx + 1;
        }

        assert(queue@ =~= students@);

        let mut sand_idx: usize = 0;
        let mut skipped: usize = 0;

        assert(sandwiches@.subrange(0, sandwiches@.len() as int) =~= sandwiches@);

        while sand_idx < sandwiches.len() && skipped < queue.len()
            invariant
                0 <= sand_idx <= sandwiches.len(),
                0 <= skipped <= queue.len(),
                queue.len() as int + sand_idx as int == students.len() as int,
                queue.len() <= 100,
                Self::simulate(
                    queue@,
                    sandwiches@.subrange(sand_idx as int, sandwiches@.len() as int),
                    skipped as nat,
                ) == Self::simulate(students@, sandwiches@, 0),
            decreases queue.len() + sandwiches.len() - sand_idx, queue.len() - skipped,
        {
            let ghost old_queue = queue@;
            let ghost rem_stack = sandwiches@.subrange(sand_idx as int, sandwiches@.len() as int);

            assert(rem_stack.len() > 0);
            assert(queue.len() > 0);
            assert(rem_stack[0] == sandwiches@[sand_idx as int]);

            if queue[0] == sandwiches[sand_idx] {
                
                assert(old_queue[0] == rem_stack[0]);

                let mut new_queue: Vec<i32> = Vec::new();
                let mut k: usize = 1;
                while k < queue.len()
                    invariant
                        1 <= k <= queue.len(),
                        new_queue@.len() == (k - 1) as int,
                        forall|j: int| 0 <= j < new_queue@.len() ==> new_queue@[j] == queue@[j + 1],
                        queue@ == old_queue,
                    decreases queue.len() - k,
                {
                    new_queue.push(queue[k]);
                    k = k + 1;
                }

                assert(new_queue@ =~= old_queue.subrange(1, old_queue.len() as int));

                assert(rem_stack.subrange(1, rem_stack.len() as int)
                    =~= sandwiches@.subrange((sand_idx + 1) as int, sandwiches@.len() as int));

                queue = new_queue;
                sand_idx = sand_idx + 1;
                skipped = 0;
            } else {
                
                assert(old_queue[0] != rem_stack[0]);

                let front: i32 = queue[0];
                let mut new_queue: Vec<i32> = Vec::new();
                let mut k: usize = 1;
                while k < queue.len()
                    invariant
                        1 <= k <= queue.len(),
                        new_queue@.len() == (k - 1) as int,
                        forall|j: int| 0 <= j < new_queue@.len() ==> new_queue@[j] == queue@[j + 1],
                        queue@ == old_queue,
                    decreases queue.len() - k,
                {
                    new_queue.push(queue[k]);
                    k = k + 1;
                }
                new_queue.push(front);

                assert(new_queue@ =~= old_queue.subrange(1, old_queue.len() as int) + seq![old_queue[0]]);

                queue = new_queue;
                skipped = skipped + 1;
            }
        }

        queue.len() as i32
    }
}

}
