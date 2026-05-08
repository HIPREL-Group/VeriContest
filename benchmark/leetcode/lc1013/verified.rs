use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(arr: Seq<i32>, end: int) -> int
        recommends
            0 <= end <= arr.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::prefix_sum(arr, end - 1) + arr[end - 1] as int
        }
    }

    pub open spec fn total_sum(arr: Seq<i32>) -> int {
        Self::prefix_sum(arr, arr.len() as int)
    }

    pub open spec fn valid_partition(arr: Seq<i32>, a: int, b: int) -> bool {
        &&& 1 <= a < b < arr.len()
        &&& {
            let s1 = Self::prefix_sum(arr, a);
            let s2 = Self::prefix_sum(arr, b) - Self::prefix_sum(arr, a);
            let s3 = Self::total_sum(arr) - Self::prefix_sum(arr, b);
            s1 == s2 && s2 == s3
        }
    }

    proof fn lemma_prefix_sum_step(arr: Seq<i32>, i: int)
        requires
            0 <= i < arr.len(),
        ensures
            Self::prefix_sum(arr, i + 1) == Self::prefix_sum(arr, i) + arr[i] as int,
    {
    }

    proof fn lemma_prefix_targets_imply_valid_partition(arr: Seq<i32>, a: int, b: int, target: int)
        requires
            1 <= a < b < arr.len(),
            Self::prefix_sum(arr, a) == target,
            Self::prefix_sum(arr, b) == 2 * target,
            Self::total_sum(arr) == 3 * target,
        ensures
            Self::valid_partition(arr, a, b),
    {
        assert(Self::prefix_sum(arr, b) - Self::prefix_sum(arr, a) == target);
        assert(Self::total_sum(arr) - Self::prefix_sum(arr, b) == target);
    }

    proof fn lemma_valid_partition_properties(arr: Seq<i32>, a: int, b: int)
        requires
            Self::valid_partition(arr, a, b),
        ensures
            Self::prefix_sum(arr, b) == 2 * Self::prefix_sum(arr, a),
            Self::total_sum(arr) == 3 * Self::prefix_sum(arr, a),
    {
        let s1 = Self::prefix_sum(arr, a);
        let s2 = Self::prefix_sum(arr, b) - Self::prefix_sum(arr, a);
        let s3 = Self::total_sum(arr) - Self::prefix_sum(arr, b);
        assert(s1 == s2);
        assert(s2 == s3);
        assert(Self::prefix_sum(arr, b) == s1 + s2);
        assert(Self::total_sum(arr) == s1 + s2 + s3);
    }

    pub fn can_three_parts_equal_sum(arr: Vec<i32>) -> (result: bool)
        requires
            3 <= arr.len() <= 50_000,
            forall |i: int| 0 <= i < arr.len() ==> -10_000 <= #[trigger] arr[i] <= 10_000,
        ensures
            result == (exists |a: int, b: int| Self::valid_partition(arr@, a, b)),
    {
        let n = arr.len();
        let mut total: i128 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == arr.len(),
                3 <= n <= 50_000,
                0 <= i <= n,
                forall |k: int| 0 <= k < n ==> -10_000 <= #[trigger] arr[k] <= 10_000,
                total as int == Self::prefix_sum(arr@, i as int),
                -10_000 * i as int <= total as int <= 10_000 * i as int,
            decreases n - i,
        {
            proof {
                Self::lemma_prefix_sum_step(arr@, i as int);
            }
            total = total + arr[i] as i128;
            i += 1;
        }

        let target = total / 3;
        if target * 3 != total {
            proof {
                assert(total as int == Self::total_sum(arr@));
                assert(!(exists |a: int, b: int| Self::valid_partition(arr@, a, b))) by {
                    assert forall |a: int, b: int| Self::valid_partition(arr@, a, b) implies false by {
                        Self::lemma_valid_partition_properties(arr@, a, b);
                        assert(total as int == 3 * Self::prefix_sum(arr@, a));
                        assert(total == 3 * (Self::prefix_sum(arr@, a) as i128));
                        assert(target == Self::prefix_sum(arr@, a) as i128);
                        assert(target * 3 == total);
                    }
                };
            }
            return false;
        }

        proof {
            assert(total as int == Self::total_sum(arr@));
            assert(target as int == total as int / 3);
            assert(total as int == 3 * target as int);
        }

        let mut prefix: i128 = 0;
        i = 0;
        while i < n - 2
            invariant
                n == arr.len(),
                3 <= n <= 50_000,
                0 <= i <= n - 2,
                forall |k: int| 0 <= k < n ==> -10_000 <= #[trigger] arr[k] <= 10_000,
                total as int == Self::total_sum(arr@),
                total as int == 3 * target as int,
                prefix as int == Self::prefix_sum(arr@, i as int),
                -10_000 * i as int <= prefix as int <= 10_000 * i as int,
                forall |a: int| (1 <= a && a <= (i as int)) ==> #[trigger] Self::prefix_sum(arr@, a) != target as int,
            decreases n - 1 - i,
        {
            proof {
                Self::lemma_prefix_sum_step(arr@, i as int);
            }
            let next_prefix = prefix + arr[i] as i128;
            proof {
                assert(next_prefix as int == prefix as int + arr@[i as int] as int);
                assert(next_prefix as int == Self::prefix_sum(arr@, i as int + 1));
            }
            prefix = next_prefix;
            if prefix == target {
                let first_end = i + 1;
                i += 1;
                while i < n - 1
                    invariant
                        n == arr.len(),
                        3 <= n <= 50_000,
                        1 <= first_end,
                        first_end < n,
                        first_end <= i,
                        i <= n - 1,
                        forall |k: int| 0 <= k < n ==> -10_000 <= #[trigger] arr[k] <= 10_000,
                        total as int == Self::total_sum(arr@),
                        total as int == 3 * target as int,
                        prefix as int == Self::prefix_sum(arr@, i as int),
                        -10_000 * i as int <= prefix as int <= 10_000 * i as int,
                        Self::prefix_sum(arr@, first_end as int) == target as int,
                        forall |a: int| (1 <= a && a < (first_end as int)) ==> #[trigger] Self::prefix_sum(arr@, a) != target as int,
                        forall |b: int| ((first_end as int) < b && b <= (i as int)) ==> #[trigger] Self::prefix_sum(arr@, b) != 2 * target as int,
                    decreases n - 1 - i,
                {
                    proof {
                        Self::lemma_prefix_sum_step(arr@, i as int);
                    }
                    let next_prefix = prefix + arr[i] as i128;
                    prefix = next_prefix;
                    if prefix == 2 * target {
                        proof {
                            Self::lemma_prefix_targets_imply_valid_partition(arr@, first_end as int, i as int + 1, target as int);
                        }
                        return true;
                    }
                    i += 1;
                }
                proof {
                    assert(!(exists |a: int, b: int| Self::valid_partition(arr@, a, b))) by {
                        assert forall |a: int, b: int| Self::valid_partition(arr@, a, b) implies false by {
                            Self::lemma_valid_partition_properties(arr@, a, b);
                        }
                    };
                }
                return false;
            }
            i += 1;
        }

        proof {
            assert(!(exists |a: int, b: int| Self::valid_partition(arr@, a, b))) by {
                assert forall |a: int, b: int| Self::valid_partition(arr@, a, b) implies false by {
                    Self::lemma_valid_partition_properties(arr@, a, b);
                    assert(Self::prefix_sum(arr@, a) == target as int);
                    assert(Self::prefix_sum(arr@, a) != target as int);
                }
            };
        }
        false
    }
}

}
