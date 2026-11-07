use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    proof fn lemma_filter_push<T>(seq: Seq<T>, x: T, f: spec_fn(T) -> bool)
        ensures
            seq.push(x).filter(f).len() == seq.filter(f).len() + if f(x) { 1 as nat } else { 0 as nat },
            seq.push(x).filter(f) =~= seq.filter(f) + (if f(x) { seq![x] } else { Seq::empty() }),
        decreases seq.len(),
    {
        reveal_with_fuel(Seq::filter, 2);

        if seq.len() == 0 {
        } else {
            let head = seq[0];
            let tail = seq.subrange(1, seq.len() as int);
            
            Self::lemma_filter_push(tail, x, f);

            assert(seq =~= seq![head] + tail);
            assert(seq.push(x) =~= seq![head] + tail.push(x));

            if f(head) {
                assert(seq.filter(f) =~= seq![head] + tail.filter(f));
                assert(seq.push(x).filter(f) =~= seq![head] + tail.push(x).filter(f));
            } else {
                assert(seq.filter(f) =~= tail.filter(f));
                assert(seq.push(x).filter(f) =~= tail.push(x).filter(f));
            }
        }
    }

    pub fn number_of_employees_who_met_target(hours: Vec<i32>, target: i32) -> (res: i32) 
        requires 
            1 <= hours.len() <= 50, 
            0 <= target <= 100_000, 
            forall |i: int| 0 <= i < hours.len() ==> 0 <= #[trigger] hours[i] <= 100_000,
        ensures
            res as int == hours@.filter(|h: i32| h >= target).len(),
            0 <= res <= hours.len(), 
    {
        let mut count = 0;
        for i in 0..hours.len() 
            invariant 
                1 <= hours.len() <= 50, 
                0 <= target <= 100_000, 
                forall |i: int| 0 <= i < hours.len() ==> 0 <= #[trigger] hours[i] <= 100_000,
                count == hours@.subrange(0, i as int).filter(|h: i32| h >= target).len(),
                0 <= count <= i as i32, 
        {
            proof {
                Self::lemma_filter_push(hours@.subrange(0, i as int), hours@[i as int], |x: i32| x >= target);
                assert(hours@.subrange(0, i as int + 1) == hours@.subrange(0, i as int).push(hours@[i as int]));
            }

            if hours[i] >= target { count += 1; }
        }

        assert(hours@.subrange(0, hours.len() as int) == hours@);

        count
    }
}

}