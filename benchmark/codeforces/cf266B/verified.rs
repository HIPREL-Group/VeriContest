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

proof fn lemma_spec_after_step(s: Seq<i32>, sec: int)
    requires
        sec >= 0,
    ensures
        spec_step_seq(spec_after_seconds(s, sec)) == spec_after_seconds(s, sec + 1),
    decreases sec,
{
    if sec == 0 {
        assert(spec_after_seconds(s, 1) == spec_after_seconds(spec_step_seq(s), 0));
        assert(spec_after_seconds(spec_step_seq(s), 0) == spec_step_seq(s));
        assert(spec_after_seconds(s, 0) == s);
        assert(spec_step_seq(spec_after_seconds(s, 0)) == spec_step_seq(s));
    } else {
        assert(spec_after_seconds(s, sec + 1) == spec_after_seconds(spec_step_seq(s), sec));
        lemma_spec_after_step(spec_step_seq(s), sec - 1);
        assert(spec_step_seq(spec_after_seconds(spec_step_seq(s), sec - 1))
            == spec_after_seconds(spec_step_seq(s), sec));
        assert(spec_after_seconds(s, sec) == spec_after_seconds(spec_step_seq(s), sec - 1));
        assert(spec_step_seq(spec_after_seconds(s, sec)) == spec_after_seconds(s, sec + 1));
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
        let ghost init = queue@;
        let n = queue.len();
        let mut cur = queue;
        let mut sec: u32 = 0;
        while sec < t
            invariant
                sec <= t,
                cur.len() == n,
                forall|j: int| 0 <= j < cur.len() as int ==> #[trigger] cur[j] == 0 || cur[j] == 1,
                cur@ == spec_after_seconds(init, sec as int),
            decreases t - sec,
        {
            let ghost cur_old = cur@;
            let mut next: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    j <= n,
                    next.len() == j,
                decreases n - j,
            {
                next.push(0i32);
                j = j + 1;
            }
            let mut i: usize = 0;
            while i < n
                invariant
                    i <= n,
                    cur.len() == n,
                    next.len() == n,
                    cur@ == cur_old,
                    forall|k: int|
                        0 <= k < i as int ==> #[trigger] next@[k] == spec_step_at(cur_old, k),
                decreases n - i,
            {
                let v = if i + 1 < n && cur[i] == 1 && cur[i + 1] == 0 {
                    0
                } else if i > 0 && cur[i - 1] == 1 && cur[i] == 0 {
                    1
                } else {
                    cur[i]
                };
                proof {
                    assert(i < n);
                    assert(i < cur_old.len());
                    if i + 1 < n && cur[i as int] == 1 && cur[i as int + 1] == 0 {
                        assert(i as int + 1 < cur_old.len());
                        assert(cur_old[i as int] == 1);
                        assert(cur_old[i as int + 1] == 0);
                        assert(spec_step_at(cur_old, i as int) == 0);
                        assert(v == 0);
                    } else if i > 0 && cur[i as int - 1] == 1 && cur[i as int] == 0 {
                        assert(cur_old[i as int - 1] == 1);
                        assert(cur_old[i as int] == 0);
                        assert(spec_step_at(cur_old, i as int) == 1);
                        assert(v == 1);
                    } else {
                        assert(!(i as int + 1 < cur_old.len() && cur_old[i as int] == 1 && cur_old[i as int + 1] == 0));
                        assert(!(i as int > 0 && cur_old[i as int - 1] == 1 && cur_old[i as int] == 0));
                        assert(spec_step_at(cur_old, i as int) == cur_old[i as int]);
                        assert(v == cur[i as int]);
                        assert(cur_old[i as int] == cur[i as int]);
                    }
                }
                next.set(i, v);
                i = i + 1;
            }
            proof {
                assert(forall|k: int|
                    0 <= k < n as int ==> #[trigger] next@[k] == spec_step_at(cur_old, k));
                assert(next@ == spec_step_seq(cur_old));
                lemma_spec_after_step(init, sec as int);
                assert(spec_step_seq(spec_after_seconds(init, sec as int)) == spec_after_seconds(init, sec as int + 1));
                assert(next@ == spec_after_seconds(init, sec as int + 1));
            }
            cur = next;
            sec = sec + 1;
        }
        proof {
            assert(cur@ == spec_after_seconds(init, sec as int));
            assert(sec == t);
            assert(cur@ == spec_after_seconds(init, t as int));
        }
        cur
    }
}

}
