use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count(s: Seq<i32>, v: i32) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            (if s[0] == v { 1int } else { 0int }) + Self::count(s.subrange(1, s.len() as int), v)
        }
    }

    proof fn count_nonneg(s: Seq<i32>, v: i32)
        ensures
            Self::count(s, v) >= 0,
        decreases s.len(),
    {
        if s.len() > 0 {
            Self::count_nonneg(s.subrange(1, s.len() as int), v);
        }
    }

    proof fn count_le_len(s: Seq<i32>, v: i32)
        ensures
            Self::count(s, v) <= s.len(),
        decreases s.len(),
    {
        if s.len() > 0 {
            Self::count_le_len(s.subrange(1, s.len() as int), v);
        }
    }

    proof fn count_no_match(s: Seq<i32>, v: i32)
        requires
            forall|k: int| 0 <= k < s.len() ==> s[k] != v,
        ensures
            Self::count(s, v) == 0,
        decreases s.len(),
    {
        if s.len() > 0 {
            let tail = s.subrange(1, s.len() as int);
            assert forall|k: int| 0 <= k < tail.len() implies tail[k] != v by {
                assert(tail[k] == s[k + 1]);
            }
            Self::count_no_match(tail, v);
        }
    }

    proof fn count_bounded_by_first_mismatch(arr: Seq<i32>, v: i32, k: int)
        requires
            arr.len() > 0,
            0 < k < arr.len(),
            arr[0] == v,
            arr[k] != v,
            forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
        ensures
            Self::count(arr, v) <= k,
        decreases arr.len(),
    {
        let tail = arr.subrange(1, arr.len() as int);
        if arr[1] == v {
            assert forall|i: int, j: int| 0 <= i < j < tail.len() implies tail[i] <= tail[j] by {
                assert(tail[i] == arr[i + 1]);
                assert(tail[j] == arr[j + 1]);
            }
            assert(tail[k - 1] == arr[k]);
            Self::count_bounded_by_first_mismatch(tail, v, k - 1);
        } else {
            assert forall|m: int| 0 <= m < tail.len() implies tail[m] != v by {
                assert(tail[m] == arr[m + 1]);
                if m + 1 > 1 {
                    assert(arr[1] <= arr[m + 1]);
                }
            }
            Self::count_no_match(tail, v);
        }
    }

    proof fn count_implies_window(arr: Seq<i32>, v: i32, k: int)
        requires
            arr.len() > 0,
            0 <= k < arr.len(),
            forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
            Self::count(arr, v) > k,
        ensures
            exists|j: int|
                0 <= j && j + k < arr.len() && #[trigger] arr[j] == v && arr[j + k] == v,
        decreases arr.len(),
    {
        if arr.len() == 1 {
            assert(k == 0) by {
                assert(k >= 0);
                assert(k < arr.len());
            }
            assert(arr.subrange(1, arr.len() as int).len() == 0);
            assert(Self::count(arr.subrange(1, arr.len() as int), v) == 0);
            assert(Self::count(arr, v) == (if arr[0] == v { 1int } else { 0int }));
            assert(arr[0] == v);
        } else if arr[0] == v && arr[k] == v {
            assert(0 <= 0int);
            assert(0int + k < arr.len() as int);
            assert(arr[0int] == v);
            assert(arr[0int + k] == v);
        } else if arr[0] == v {
            if k == 0 {
                assert(false);
            } else {
                Self::count_bounded_by_first_mismatch(arr, v, k);
                assert(false);
            }
        } else {
            let tail = arr.subrange(1, arr.len() as int);
            assert forall|i: int, j: int| 0 <= i < j < tail.len() implies tail[i] <= tail[j] by {
                assert(tail[i] == arr[i + 1]);
                assert(tail[j] == arr[j + 1]);
            }
            Self::count_le_len(tail, v);
            Self::count_implies_window(tail, v, k);
            let j = choose|j: int|
                0 <= j && j + k < tail.len() && #[trigger] tail[j] == v && tail[j + k] == v;
            assert(arr[j + 1] == tail[j]);
            assert(arr[j + 1 + k] == tail[j + k]);
            assert(0 <= j + 1);
            assert(j + 1 + k < arr.len() as int);
            assert(arr[j + 1] == v);
            assert(arr[j + 1 + k] == v);
        }
    }

    proof fn count_ge_matching_range(s: Seq<i32>, v: i32, lo: int, hi: int)
        requires
            0 <= lo <= hi <= s.len(),
            forall|j: int| lo <= j < hi ==> s[j] == v,
        ensures
            Self::count(s, v) >= hi - lo,
        decreases s.len(),
    {
        if s.len() == 0 || lo >= hi {
            Self::count_nonneg(s, v);
        } else if lo == 0 {
            let tail = s.subrange(1, s.len() as int);
            if hi == 1 {
                Self::count_nonneg(tail, v);
            } else {
                assert forall|j: int| 0 <= j < hi - 1 implies tail[j] == v by {
                    assert(tail[j] == s[j + 1]);
                }
                Self::count_ge_matching_range(tail, v, 0, hi - 1);
            }
        } else {
            let tail = s.subrange(1, s.len() as int);
            assert forall|j: int| lo - 1 <= j < hi - 1 implies tail[j] == v by {
                assert(tail[j] == s[j + 1]);
            }
            Self::count_ge_matching_range(tail, v, lo - 1, hi - 1);
        }
    }

    proof fn sorted_range_equal(arr: Seq<i32>, a: int, b: int)
        requires
            forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
            0 <= a <= b < arr.len(),
            arr[a] == arr[b],
        ensures
            forall|k: int| a <= k <= b ==> arr[k] == arr[a],
    {
        assert forall|k: int| a <= k <= b implies arr[k] == arr[a] by {
            if k > a {
                assert(arr[a] <= arr[k]);
            }
            if k < b {
                assert(arr[k] <= arr[b]);
            }
        }
    }

    pub fn find_special_integer(arr: Vec<i32>) -> (res: i32)
        requires
            1 <= arr.len() <= 10_000,
            forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 100_000,
            forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
            exists|v: i32| #[trigger] Self::count(arr@, v) > arr.len() as int / 4,
            forall|v1: i32, v2: i32| (Self::count(arr@, v1) > arr.len() as int / 4
                && Self::count(arr@, v2) > arr.len() as int / 4) ==> v1 == v2,
        ensures
            Self::count(arr@, res) > arr.len() as int / 4,
    {
        let n = arr.len();
        let quarter = n / 4;
        proof {
            let v = choose|v: i32| #[trigger] Self::count(arr@, v) > arr.len() as int / 4;
            Self::count_implies_window(arr@, v, quarter as int);
        }
        let mut i: usize = 0;
        while i + quarter < n
            invariant
                0 <= i <= n,
                n == arr.len(),
                quarter == n / 4,
                1 <= arr.len() <= 10_000,
                forall|ii: int| 0 <= ii < arr.len() ==> 0 <= #[trigger] arr[ii] <= 100_000,
                forall|ii: int, jj: int| 0 <= ii < jj < arr.len() ==> arr[ii] <= arr[jj],
                exists|j: int|
                    i as int <= j && j + (quarter as int) < n as int && #[trigger] arr@[j]
                        == arr@[j + quarter as int],
            decreases n - i,
        {
            if arr[i] == arr[i + quarter] {
                proof {
                    Self::sorted_range_equal(
                        arr@,
                        i as int,
                        (i + quarter) as int,
                    );
                    Self::count_ge_matching_range(
                        arr@,
                        arr@[i as int],
                        i as int,
                        (i + quarter + 1) as int,
                    );
                }
                return arr[i];
            }
            proof {
                let j = choose|j: int|
                    i as int <= j && j + (quarter as int) < n as int && #[trigger] arr@[j]
                        == arr@[j + quarter as int];
                assert(j != i as int);
            }
            i += 1;
        }
        proof {
            let j = choose|j: int|
                i as int <= j && j + (quarter as int) < n as int && #[trigger] arr@[j]
                    == arr@[j + quarter as int];
            assert(false);
        }
        arr[0]
    }
}

}
