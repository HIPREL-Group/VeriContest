use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn in_circular_range(s: int, start: int, end: int, n: int) -> bool {
        if start <= end {
            start <= s && s <= end
        } else {
            (1 <= s && s <= end) || (start <= s && s <= n)
        }
    }

    pub fn most_visited(n: i32, rounds: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= n <= 100,
            rounds.len() >= 2,
            rounds.len() <= 101,
            forall |i: int| 0 <= i < rounds.len() ==> 1 <= #[trigger] rounds[i] <= n,
            forall |i: int| 0 <= i < rounds.len() - 1 ==> (#[trigger] rounds[i]) != rounds[i + 1],
        ensures
            result@.len() >= 1,
            forall |i: int| 0 <= i < result@.len() ==> 1 <= #[trigger] result@[i] <= n,
            forall |i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
            forall |i: int| 0 <= i < result@.len() ==>
                Self::in_circular_range(
                    (#[trigger] result@[i]) as int,
                    rounds[0] as int,
                    rounds[rounds.len() - 1] as int,
                    n as int,
                ),
            forall |s: int| 1 <= s <= n as int && (#[trigger] Self::in_circular_range(
                s,
                rounds[0] as int,
                rounds[rounds.len() - 1] as int,
                n as int,
            )) ==> exists |i: int| 0 <= i < result@.len() && result@[i] as int == s,
    {
        let start = rounds[0];
        let end_val = rounds[rounds.len() - 1];
        let mut result: Vec<i32> = Vec::new();
        if start <= end_val {
            let mut s = start;
            while s <= end_val
                invariant
                    1 <= start <= end_val <= n <= 100,
                    start <= s <= end_val + 1,
                    result@.len() == (s - start) as int,
                    forall |i: int| 0 <= i < result@.len() ==> (#[trigger] result@[i]) as int == start as int + i,
                decreases end_val - s + 1,
            {
                result.push(s);
                s = s + 1;
            }
            proof {
                assert forall |i: int, j: int| 0 <= i < j < result@.len() implies result@[i] < result@[j] by {}

                assert forall |i: int| 0 <= i < result@.len() implies
                    Self::in_circular_range(
                        (#[trigger] result@[i]) as int,
                        start as int,
                        end_val as int,
                        n as int,
                    ) by {}

                assert forall |sv: int| 1 <= sv <= n as int && Self::in_circular_range(
                    sv, start as int, end_val as int, n as int,
                ) implies exists |i: int| 0 <= i < result@.len() && result@[i] as int == sv by {
                    let idx = sv - start as int;
                    assert(result@[idx] as int == sv);
                }
            }
        } else {
            let mut s: i32 = 1;
            while s <= end_val
                invariant
                    1 <= end_val < start <= n <= 100,
                    1 <= s <= end_val + 1,
                    result@.len() == (s - 1) as int,
                    forall |i: int| 0 <= i < result@.len() ==> (#[trigger] result@[i]) as int == i + 1,
                decreases end_val - s + 1,
            {
                result.push(s);
                s = s + 1;
            }
            let ghost first_part_len: int = result@.len() as int;
            s = start;
            while s <= n
                invariant
                    1 <= end_val < start <= n <= 100,
                    start <= s <= n + 1,
                    first_part_len == end_val as int,
                    result@.len() as int == first_part_len + (s - start) as int,
                    forall |i: int| 0 <= i < first_part_len ==> (#[trigger] result@[i]) as int == i + 1,
                    forall |i: int| first_part_len <= i < result@.len() ==> (#[trigger] result@[i]) as int == start as int + (i - first_part_len),
                decreases n - s + 1,
            {
                result.push(s);
                s = s + 1;
            }

            proof {
                assert forall |i: int, j: int| 0 <= i < j < result@.len() implies result@[i] < result@[j] by {
                    if i < first_part_len && j < first_part_len {
                    } else if i >= first_part_len && j >= first_part_len {
                    } else {
                        assert(result@[i] as int <= end_val as int);
                        assert(result@[j] as int >= start as int);
                    }
                }

                assert forall |i: int| 0 <= i < result@.len() implies
                    Self::in_circular_range(
                        (#[trigger] result@[i]) as int,
                        start as int,
                        end_val as int,
                        n as int,
                    ) by {
                    if i < first_part_len {
                        assert(1 <= result@[i] as int && result@[i] as int <= end_val as int);
                    } else {
                        assert(start as int <= result@[i] as int && result@[i] as int <= n as int);
                    }
                }

                assert forall |sv: int| 1 <= sv <= n as int && Self::in_circular_range(
                    sv, start as int, end_val as int, n as int,
                ) implies exists |i: int| 0 <= i < result@.len() && result@[i] as int == sv by {
                    if sv <= end_val as int {
                        let idx = sv - 1;
                        assert(result@[idx] as int == sv);
                    } else {
                        let idx = first_part_len + (sv - start as int);
                        assert(result@[idx] as int == sv);
                    }
                }
            }
        }
        result
    }
}

}
