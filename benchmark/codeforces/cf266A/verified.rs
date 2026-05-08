use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn adjacent_pair_equal(seq: Seq<u8>, i: int) -> bool {
    0 <= i < seq.len() - 1 && seq[i] as int == seq[i + 1] as int
}

pub open spec fn count_adjacent_equal(seq: Seq<u8>, n: int) -> nat
    recommends
        0 <= n <= seq.len(),
    decreases n,
{
    if n <= 1 {
        0nat
    } else {
        let prev = count_adjacent_equal(seq, n - 1);
        if adjacent_pair_equal(seq, n - 2) {
            prev + 1nat
        } else {
            prev
        }
    }
}

pub open spec fn no_adjacent_equal(seq: Seq<u8>, n: int) -> bool {
    forall|i: int| 0 <= i < n - 1 ==> #[trigger] seq[i] as int != seq[i + 1] as int
}

proof fn lemma_count_step(seq: Seq<u8>, k: int)
    requires
        0 <= k,
        k + 1 <= seq.len(),
    ensures
        count_adjacent_equal(seq, k + 2) == count_adjacent_equal(seq, k + 1)
            + (if adjacent_pair_equal(seq, k) { 1nat } else { 0nat }),
    decreases k,
{
    reveal_with_fuel(count_adjacent_equal, 2);
}

impl Solution {
    pub fn min_stones_to_remove(colors: Vec<u8>, n: usize) -> (result: usize)
        requires
            1 <= n <= 50,
            colors.len() == n,
            forall|i: int| 0 <= i < colors.len() ==> 0 <= #[trigger] colors[i] as int <= 2,
        ensures
            result as nat == count_adjacent_equal(colors@, n as int),
    {
        let mut count = 0usize;
        let mut i = 0usize;
        while i + 1 < n
            invariant
                1 <= n <= 50,
                colors.len() == n,
                forall|j: int| 0 <= j < colors.len() ==> 0 <= #[trigger] colors[j] as int <= 2,
                0 <= i,
                i + 1 <= n,
                count <= i,
                count as nat == count_adjacent_equal(colors@, (i + 1) as int),
            decreases n - i,
        {
            proof {
                lemma_count_step(colors@, i as int);
                assert(adjacent_pair_equal(colors@, i as int) == (colors@[i as int] as int == colors@[i as int + 1] as int));
            }
            if colors[i] == colors[i + 1] {
                count += 1;
            }
            i += 1;
        }
        count
    }
}

}
