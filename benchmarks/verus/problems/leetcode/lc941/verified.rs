use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_mountain(s: Seq<i32>, peak: int) -> bool {
        s.len() >= 3
        && 0 < peak < s.len() - 1
        && (forall |a: int, b: int| 0 <= a < b <= peak ==> s[a] < s[b])
        && (forall |a: int, b: int| peak <= a < b < s.len() ==> s[a] > s[b])
    }

    pub fn valid_mountain_array(arr: Vec<i32>) -> (result: bool)
        requires
            1 <= arr.len() <= 10_000,
            forall |k: int| 0 <= k < arr.len() ==> 0 <= #[trigger] arr[k] <= 10_000,
        ensures
            result == (exists |peak: int| Self::is_mountain(arr@, peak)),
    {
        let n = arr.len();
        if n < 3 {
            proof {
                assert forall |p: int| !Self::is_mountain(arr@, p) by {};
            }
            return false;
        }

        let mut i: usize = 0;

        while i + 1 < n && arr[i] < arr[i + 1]
            invariant
                0 <= i < n,
                n == arr.len(),
                1 <= n <= 10_000,
                n >= 3,
                forall |k: int| 0 <= k < n ==> 0 <= #[trigger] arr[k] <= 10_000,
                forall |a: int, b: int| 0 <= a < b <= i as int ==> arr[a] < arr[b],
            decreases n - i,
        {
            i = i + 1;
        }

        if i == 0 {
            proof {
                assert forall |p: int| !Self::is_mountain(arr@, p) by {
                    if 0 < p < arr@.len() - 1 {
                        assert(arr@[0] >= arr@[1]);
                    }
                };
            }
            return false;
        }

        if i == n - 1 {
            proof {
                assert forall |p: int| !Self::is_mountain(arr@, p) by {
                    if 0 < p < arr@.len() - 1 {
                        assert(arr@[p] < arr@[p + 1]);
                    }
                };
            }
            return false;
        }

        let peak = i;

        while i + 1 < n && arr[i] > arr[i + 1]
            invariant
                peak <= i < n,
                n == arr.len(),
                1 <= n <= 10_000,
                0 < peak < n - 1,
                forall |k: int| 0 <= k < n ==> 0 <= #[trigger] arr[k] <= 10_000,
                forall |a: int, b: int| 0 <= a < b <= peak as int ==> arr[a] < arr[b],
                forall |a: int, b: int| peak as int <= a < b <= i as int ==> arr[a] > arr[b],
                arr@[peak as int] >= arr@[(peak + 1) as int],
            decreases n - i,
        {
            i = i + 1;
        }

        if i == n - 1 {
            proof {
                assert(Self::is_mountain(arr@, peak as int));
            }
            return true;
        } else {
            proof {
                assert forall |p: int| !Self::is_mountain(arr@, p) by {
                    if 0 < p < arr@.len() - 1 {
                        if p > peak as int {
                            assert(arr@[peak as int] >= arr@[(peak + 1) as int]);
                            assert(0int <= peak as int && (peak as int) + 1 <= p);
                        } else {
                            assert(p <= i as int);
                            assert((i as int) + 1 < arr@.len() as int);
                            assert(arr@[i as int] <= arr@[(i + 1) as int]);
                        }
                    }
                };
            }
            return false;
        }
    }
}

}
