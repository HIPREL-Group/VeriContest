use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn level_in_seq(seq: Seq<i32>, level: int) -> bool {
    exists|i: int| 0 <= i < seq.len() && #[trigger] seq[i] == level
}

pub open spec fn level_passable(level: int, x_levels: Seq<i32>, y_levels: Seq<i32>) -> bool {
    level_in_seq(x_levels, level) || level_in_seq(y_levels, level)
}

impl Solution {
    pub fn can_be_the_guy(n: i32, x_levels: Vec<i32>, y_levels: Vec<i32>) -> (res: bool)
        requires
            1 <= n <= 100,
            forall|i: int| 0 <= i < x_levels.len() ==> 1 <= #[trigger] x_levels[i] && x_levels[i] <= n,
            forall|i: int| 0 <= i < y_levels.len() ==> 1 <= #[trigger] y_levels[i] && y_levels[i] <= n,
        ensures
            res == (forall|k: int| 1 <= k && k <= (n as int) ==> #[trigger] level_passable(k, x_levels@, y_levels@)),
    {
        let mut k = 1i32;
        while k <= n
            invariant
                1 <= k <= (n as int) + 1,
                (n as int) <= 100,
                forall|level: int| 1 <= level && level < k ==> #[trigger] level_passable(level, x_levels@, y_levels@),
            decreases
                (n as int) + 1 - k,
        {
            let x_len = x_levels.len();
            let y_len = y_levels.len();
            let mut found = false;
            let mut i = 0usize;
            while i < x_len && !found
                invariant
                    0 <= i <= x_len,
                    x_len == x_levels.len(),
                    forall|j: int| 0 <= j && j < (i as int) ==> (x_levels[j] as int) != (k as int),
                    (i as int) >= (x_len as int) ==> (forall|j: int| 0 <= j && j < (x_len as int) ==> (x_levels[j] as int) != (k as int)),
                    found ==> #[trigger] level_in_seq(x_levels@, k as int),
                decreases
                    (if found { 0int } else { 1int }),
                    (x_len - i) as int,
            {
                if x_levels[i] == k {
                    proof {
                        assert(x_levels@[i as int] == k as int);
                        assert(level_in_seq(x_levels@, k as int));
                        assert(level_passable(k as int, x_levels@, y_levels@));
                    }
                    found = true;
                } else {
                    i += 1;
                }
            }
            proof {
                if found {
                    assert(level_in_seq(x_levels@, k as int));
                    assert(level_passable(k as int, x_levels@, y_levels@));
                }
            }
            if !found {
                proof {
                    assert(!(i < x_len && !found));
                    assert((i as int) >= (x_len as int) || found);
                    assert((i as int) >= (x_len as int));
                    assert(forall|j: int| 0 <= j && j < (x_len as int) ==> (x_levels[j] as int) != (k as int));
                }
                i = 0;
                while i < y_len && !found
                    invariant
                        0 <= i <= y_len,
                        y_len == y_levels.len(),
                        x_len == x_levels.len(),
                        forall|j: int| 0 <= j && j < (i as int) ==> (y_levels[j] as int) != (k as int),
                        forall|j: int| 0 <= j && j < (x_len as int) ==> (x_levels[j] as int) != (k as int),
                        (i as int) >= (y_len as int) ==> (forall|j: int| 0 <= j && j < (y_len as int) ==> (y_levels[j] as int) != (k as int)),
                        found ==> #[trigger] level_passable(k as int, x_levels@, y_levels@),
                    decreases
                        (if found { 0int } else { 1int }),
                        (y_len - i) as int,
                {
                    if y_levels[i] == k {
                        proof {
                            assert(y_levels@[i as int] == k as int);
                            assert(level_in_seq(y_levels@, k as int));
                            assert(level_passable(k as int, x_levels@, y_levels@));
                        }
                        found = true;
                    } else {
                        i += 1;
                    }
                }
                proof {
                    assert(!(i < y_len && !found));
                    assert((i as int) >= (y_len as int) || found);
                    if !found {
                        assert((i as int) >= (y_len as int));
                    }
                }
            }
            if !found {
                proof {
                    assert((i as int) >= (y_len as int));
                    assert(forall|j: int| 0 <= j && j < (y_len as int) ==> (y_levels[j] as int) != (k as int));
                    assert(!level_in_seq(x_levels@, k as int));
                    assert(!level_in_seq(y_levels@, k as int));
                    assert(!level_passable(k as int, x_levels@, y_levels@));
                }
                return false;
            }
            proof {
                assert(found);
                assert(level_passable(k as int, x_levels@, y_levels@));
                assert((k as int) <= (n as int));
                assert(1 <= k);
                assert((k as int) + 1 <= (n as int) + 1);
                assert((k as int) <= 100);
            }
            k += 1;
        }
        true
    }
}

}
