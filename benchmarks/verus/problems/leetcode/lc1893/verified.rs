use vstd::prelude::*;

fn main() {}

verus! {
pub struct Solution;

pub open spec fn is_covered_spec(ranges: Seq<Vec<i32>>, x: int) -> bool {
    exists |j: int| 0 <= j < ranges.len() && #[trigger] ranges[j][0] <= x && x <= ranges[j][1]
}

impl Solution {
    pub fn is_covered(ranges: Vec<Vec<i32>>, left: i32, right: i32) -> (result: bool)
        requires
            1 <= ranges.len() <= 50,
            1 <= left <= right <= 50,
            forall |j: int| 0 <= j < ranges.len() ==> #[trigger] ranges[j]@.len() == 2,
            forall |j: int| 0 <= j < ranges.len() ==> 1 <= #[trigger] ranges[j][0] && ranges[j][0] <= ranges[j][1] && ranges[j][1] <= 50,
        ensures
            result <==> forall |i: int| left <= i <= right ==> #[trigger] is_covered_spec(ranges@, i),
    {
        let mut i = left;
        while i <= right
            invariant
                left <= i <= right + 1,
                left <= right,
                forall |ii: int| left <= ii < i ==> #[trigger] is_covered_spec(ranges@, ii),
                1 <= ranges.len() <= 50,
                forall |j: int| 0 <= j < ranges.len() ==> #[trigger] ranges[j]@.len() == 2,
                forall |j: int| 0 <= j < ranges.len() ==> 1 <= #[trigger] ranges[j][0] && ranges[j][0] <= ranges[j][1] && ranges[j][1] <= 50
            decreases right - i + 1
        {
            let mut covered = false;
            let mut j = 0;
            while j < ranges.len()
                invariant
                    0 <= j <= ranges.len(),
                    1 <= ranges.len() <= 50,
                    left <= i <= right,
                    forall |k: int| 0 <= k < ranges.len() ==> #[trigger] ranges[k]@.len() == 2,
                    covered <==> exists |k: int| 0 <= k < j && #[trigger] ranges[k][0] <= i && i <= ranges[k][1]
                decreases ranges.len() - j
            {
                if ranges[j][0] <= i && i <= ranges[j][1] {
                    covered = true;
                }
                j += 1;
            }
            if !covered {
                proof {
                    assert(!is_covered_spec(ranges@, i as int));
                }
                return false;
            }
            proof {
                assert(is_covered_spec(ranges@, i as int));
            }
            i += 1;
        }
        true
    }
}
}
