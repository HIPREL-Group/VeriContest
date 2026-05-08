use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn alt_at(arr: Seq<i32>, i: int) -> bool {
        2 <= i < arr.len()
        && ((arr[i - 2] < arr[i - 1] && arr[i - 1] > arr[i])
            || (arr[i - 2] > arr[i - 1] && arr[i - 1] < arr[i]))
    }

    pub open spec fn is_turbulent(arr: Seq<i32>, start: int, end: int) -> bool {
        0 <= start <= end < arr.len()
        && (forall |k: int| start < k <= end ==> #[trigger] arr[k - 1] != arr[k])
        && (forall |k: int| start + 2 <= k <= end ==> #[trigger] Self::alt_at(arr, k))
    }

    pub open spec fn turbulent_len(arr: Seq<i32>, start: int, len: int) -> bool {
        1 <= len
        && start + len <= arr.len()
        && Self::is_turbulent(arr, start, start + len - 1)
    }

    pub open spec fn run_at(arr: Seq<i32>, i: int) -> nat
        decreases i
    {
        if i <= 0 {
            1
        } else if i == 1 {
            if arr[0] != arr[1] { 2 } else { 1 }
        } else if Self::alt_at(arr, i) {
            Self::run_at(arr, i - 1) + 1
        } else if arr[i - 1] != arr[i] {
            2
        } else {
            1
        }
    }

    pub open spec fn max_run(arr: Seq<i32>, i: int) -> nat
        decreases i
    {
        if i <= 0 {
            1
        } else {
            let prev = Self::max_run(arr, i - 1);
            let cur = Self::run_at(arr, i);
            if cur > prev { cur } else { prev }
        }
    }

    proof fn lemma_singleton_turbulent(arr: Seq<i32>, i: int)
        requires
            0 <= i < arr.len(),
        ensures
            Self::is_turbulent(arr, i, i),
    {
    }

    proof fn lemma_pair_turbulent(arr: Seq<i32>, i: int)
        requires
            1 <= i < arr.len(),
            arr[i - 1] != arr[i],
        ensures
            Self::is_turbulent(arr, i - 1, i),
    {
        assert forall |k: int| i - 1 < k <= i implies #[trigger] arr[k - 1] != arr[k] by {
            assert(k == i);
        };
    }

    proof fn lemma_run_at_bounds(arr: Seq<i32>, i: int)
        requires
            0 <= i < arr.len(),
        ensures
            1 <= Self::run_at(arr, i) <= i + 1,
        decreases i,
    {
        if i > 1 && Self::alt_at(arr, i) {
            Self::lemma_run_at_bounds(arr, i - 1);
        }
    }

    proof fn lemma_unequal_implies_run_at_ge_two(arr: Seq<i32>, i: int)
        requires
            1 <= i < arr.len(),
            arr[i - 1] != arr[i],
        ensures
            Self::run_at(arr, i) >= 2,
        decreases i,
    {
        if i > 1 && Self::alt_at(arr, i) {
            Self::lemma_run_at_bounds(arr, i - 1);
        }
    }

    proof fn lemma_turbulent_prefix(arr: Seq<i32>, start: int, end: int)
        requires
            Self::is_turbulent(arr, start, end),
            start < end,
        ensures
            Self::is_turbulent(arr, start, end - 1),
    {
        assert forall |k: int| start < k <= end - 1 implies #[trigger] arr[k - 1] != arr[k] by {
            assert(arr[k - 1] != arr[k]);
        };
        assert forall |k: int| start + 2 <= k <= end - 1 implies #[trigger] Self::alt_at(arr, k) by {
            assert(Self::alt_at(arr, k));
        };
    }

    proof fn lemma_extend_turbulent(arr: Seq<i32>, start: int, end: int)
        requires
            Self::is_turbulent(arr, start, end),
            start < end,
            end + 1 < arr.len(),
            Self::alt_at(arr, end + 1),
        ensures
            Self::is_turbulent(arr, start, end + 1),
    {
        assert forall |k: int| start < k <= end + 1 implies #[trigger] arr[k - 1] != arr[k] by {
            if k <= end {
                assert(arr[k - 1] != arr[k]);
            } else {
                assert(Self::alt_at(arr, end + 1));
                assert(arr[end] != arr[end + 1]);
            }
        };
        assert forall |k: int| start + 2 <= k <= end + 1 implies #[trigger] Self::alt_at(arr, k) by {
            if k <= end {
                assert(Self::alt_at(arr, k));
            } else {
                assert(Self::alt_at(arr, end + 1));
            }
        };
    }

    proof fn lemma_run_at_turbulent(arr: Seq<i32>, i: int)
        requires
            0 <= i < arr.len(),
        ensures
            Self::is_turbulent(arr, i - Self::run_at(arr, i) as int + 1, i),
        decreases i,
    {
        if i == 0 {
            Self::lemma_singleton_turbulent(arr, 0);
        } else if i == 1 {
            if arr[0] != arr[1] {
                Self::lemma_pair_turbulent(arr, 1);
            } else {
                Self::lemma_singleton_turbulent(arr, 1);
            }
        } else if Self::alt_at(arr, i) {
            Self::lemma_unequal_implies_run_at_ge_two(arr, i - 1);
            Self::lemma_run_at_turbulent(arr, i - 1);
            let start = i - Self::run_at(arr, i) as int + 1;
            let prev_start = (i - 1) - Self::run_at(arr, i - 1) as int + 1;
            assert(Self::run_at(arr, i) == Self::run_at(arr, i - 1) + 1);
            assert(start == prev_start);
            assert(prev_start < i - 1);
            Self::lemma_extend_turbulent(arr, prev_start, i - 1);
        } else if arr[i - 1] != arr[i] {
            assert(i - Self::run_at(arr, i) as int + 1 == i - 1);
            Self::lemma_pair_turbulent(arr, i);
        } else {
            assert(i - Self::run_at(arr, i) as int + 1 == i);
            Self::lemma_singleton_turbulent(arr, i);
        }
    }

    proof fn lemma_turbulent_implies_run_at(arr: Seq<i32>, start: int, end: int)
        requires
            Self::is_turbulent(arr, start, end),
        ensures
            end - start + 1 <= Self::run_at(arr, end),
        decreases end - start,
    {
        if start == end {
            Self::lemma_run_at_bounds(arr, end);
        } else if start + 1 == end {
            Self::lemma_unequal_implies_run_at_ge_two(arr, end);
        } else {
            Self::lemma_turbulent_prefix(arr, start, end);
            Self::lemma_turbulent_implies_run_at(arr, start, end - 1);
            assert(Self::alt_at(arr, end));
            assert(Self::run_at(arr, end) == Self::run_at(arr, end - 1) + 1);
        }
    }

    proof fn lemma_max_run_ge(arr: Seq<i32>, i: int, j: int)
        requires
            0 <= j <= i < arr.len(),
        ensures
            Self::max_run(arr, i) >= Self::run_at(arr, j),
        decreases i,
    {
        if i > j {
            Self::lemma_max_run_ge(arr, i - 1, j);
        }
    }

    pub fn max_turbulence_size(arr: Vec<i32>) -> (result: i32)
        requires
            1 <= arr.len() <= 40_000,
            forall |i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 1_000_000_000,
        ensures
            1 <= result,
            result as int <= arr.len(),
            exists |start: int|
                0 <= start && start + result <= arr.len()
                && #[trigger] Self::turbulent_len(arr@, start, result as int),
            forall |start: int, len: int|
                0 <= start && 1 <= len && start + len <= arr.len() as int && len > result as int
                ==> !#[trigger] Self::turbulent_len(arr@, start, len),
    {
        let n = arr.len();
        let mut best: usize = 1;
        let mut cur: usize = 1;
        let mut i: usize = 1;
        let ghost mut best_end: int = 0;

        while i < n
            invariant
                n == arr.len(),
                1 <= n <= 40_000,
                1 <= i <= n,
                forall |k: int| 0 <= k < arr.len() ==> 0 <= #[trigger] arr[k] <= 1_000_000_000,
                cur as nat == Self::run_at(arr@, i as int - 1),
                best as nat == Self::max_run(arr@, i as int - 1),
                1 <= cur <= i,
                1 <= best <= i,
                0 <= best_end < i as int,
                Self::run_at(arr@, best_end) == best as nat,
            decreases n - i,
        {
            if i >= 2
                && ((arr[i - 2] < arr[i - 1] && arr[i - 1] > arr[i])
                    || (arr[i - 2] > arr[i - 1] && arr[i - 1] < arr[i]))
            {
                proof {
                    Self::lemma_run_at_bounds(arr@, i as int - 1);
                    assert(cur < usize::MAX);
                }
                cur = cur + 1;
            } else if arr[i - 1] != arr[i] {
                cur = 2;
            } else {
                cur = 1;
            }

            if cur > best {
                best = cur;
                proof {
                    best_end = i as int;
                }
            }

            proof {
                if i >= 2 && ((arr@[(i - 2) as int] < arr@[(i - 1) as int] && arr@[(i - 1) as int] > arr@[i as int])
                    || (arr@[(i - 2) as int] > arr@[(i - 1) as int] && arr@[(i - 1) as int] < arr@[i as int])) {
                    assert(Self::alt_at(arr@, i as int));
                    assert(Self::run_at(arr@, i as int) == Self::run_at(arr@, i as int - 1) + 1);
                } else if arr@[(i - 1) as int] != arr@[i as int] {
                    if i == 1 {
                        assert(Self::run_at(arr@, i as int) == 2);
                    } else {
                        assert(!Self::alt_at(arr@, i as int));
                        assert(Self::run_at(arr@, i as int) == 2);
                    }
                } else {
                    if i == 1 {
                        assert(Self::run_at(arr@, i as int) == 1);
                    } else {
                        assert(!Self::alt_at(arr@, i as int));
                        assert(Self::run_at(arr@, i as int) == 1);
                    }
                }
                assert(cur as nat == Self::run_at(arr@, i as int));
                assert(Self::max_run(arr@, i as int)
                    == (if Self::run_at(arr@, i as int) > Self::max_run(arr@, i as int - 1)
                        { Self::run_at(arr@, i as int) }
                        else { Self::max_run(arr@, i as int - 1) }));
                assert(best as nat == Self::max_run(arr@, i as int));
            }

            i = i + 1;
        }

        proof {
            let end = best_end;
            let start = end - best as int + 1;

            Self::lemma_run_at_turbulent(arr@, end);
            Self::lemma_run_at_bounds(arr@, end);
            assert(Self::is_turbulent(arr@, start, end));
            assert(Self::turbulent_len(arr@, start, best as int));
            assert(start + best as int <= n as int);

            assert forall |s: int, len: int|
                0 <= s && 1 <= len && s + len <= n as int && len > best as int
                implies !#[trigger] Self::turbulent_len(arr@, s, len) by {
                if Self::turbulent_len(arr@, s, len) {
                    let end2 = s + len - 1;
                    Self::lemma_turbulent_implies_run_at(arr@, s, end2);
                    Self::lemma_max_run_ge(arr@, n as int - 1, end2);
                    assert(Self::max_run(arr@, n as int - 1) >= len as nat);
                    assert(Self::max_run(arr@, n as int - 1) == best as nat);
                    assert(false);
                }
            };

            assert(best <= i32::MAX as usize);
        }

        best as i32
    }
}

}
