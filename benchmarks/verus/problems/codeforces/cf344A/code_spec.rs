use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn magnet_valid(seq: Seq<u8>, i: int) -> bool {
    0 <= i < seq.len() && (#[trigger] seq[i] as int == 0 || seq[i] as int == 1)
}

pub open spec fn magnets_valid(seq: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < seq.len() ==> magnet_valid(seq, i)
}

pub open spec fn count_transitions(seq: Seq<u8>, end: int) -> nat
    recommends
        0 <= end <= seq.len(),
    decreases end,
{
    if end <= 1 {
        0nat
    } else {
        let prev = count_transitions(seq, end - 1);
        if seq[end - 1] as int != seq[end - 2] as int {
            prev + 1nat
        } else {
            prev
        }
    }
}

impl Solution {
    pub fn count_magnet_groups(magnets: Vec<u8>) -> (res: u32)
        requires
            1 <= magnets.len() <= 100000,
            magnets_valid(magnets@),
        ensures
            res as nat == 1 + count_transitions(magnets@, magnets@.len() as int),
    {
        let n = magnets.len();
        let mut groups = 1u32;
        let mut i = 1usize;
        while i < n {
            if magnets[i] != magnets[i - 1] {
                groups += 1;
            }
            i += 1;
        }
        groups
    }
}

}
