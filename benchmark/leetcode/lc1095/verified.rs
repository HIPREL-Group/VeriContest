use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub struct MountainArray {
    pub data: Vec<i32>,
}

impl MountainArray {
    pub fn get(&self, index: i32) -> (result: i32)
        requires
            0 <= index < self.data.len(),
        ensures
            result == self.data@[index as int],
    {
        self.data[index as usize]
    }

    pub fn length(&self) -> (result: i32)
        requires
            self.data@.len() <= 10_000,
        ensures
            result as int == self.data@.len(),
    {
        self.data.len() as i32
    }
}

impl Solution {
    pub open spec fn is_mountain(s: Seq<i32>, peak: int) -> bool {
        s.len() >= 3
        && 0 < peak < s.len() - 1
        && (forall |a: int, b: int| 0 <= a < b <= peak ==> s[a] < s[b])
        && (forall |a: int, b: int| peak <= a < b < s.len() ==> s[a] > s[b])
    }

    pub fn find_in_mountain_array(target: i32, mountain_arr: &MountainArray) -> (result: i32)
        requires
            3 <= mountain_arr.data.len() <= 10_000,
            forall |i: int| 0 <= i < mountain_arr.data.len() ==> 0 <= #[trigger] mountain_arr.data@[i] <= 1_000_000_000,
            0 <= target <= 1_000_000_000,
            exists |peak: int| Self::is_mountain(mountain_arr.data@, peak),
        ensures
            -1 <= result < mountain_arr.data.len(),
            result == -1 ==> forall |j: int| 0 <= j < mountain_arr.data.len() ==> mountain_arr.data@[j] != target,
            result >= 0 ==> (
                mountain_arr.data@[result as int] == target
                && forall |j: int| 0 <= j < result as int ==> mountain_arr.data@[j] != target
            ),
    {
        let n = mountain_arr.length();
        let ghost peak_idx: int = choose |p: int| Self::is_mountain(mountain_arr.data@, p);

        let mut left: i32 = 0;
        let mut right: i32 = n - 1;
        while left < right
            invariant
                0 <= left <= right < n,
                n == mountain_arr.data.len(),
                3 <= n <= 10_000,
                forall |i: int| 0 <= i < n as int ==> 0 <= #[trigger] mountain_arr.data@[i] <= 1_000_000_000,
                Self::is_mountain(mountain_arr.data@, peak_idx),
                left as int <= peak_idx,
                peak_idx <= right as int,
            decreases right - left,
        {
            let mid = left + (right - left) / 2;
            if mountain_arr.get(mid) < mountain_arr.get(mid + 1) {
                proof {
                    if peak_idx <= mid as int {
                        assert(mountain_arr.data@[mid as int] > mountain_arr.data@[mid as int + 1]);
                    }
                }
                left = mid + 1;
            } else {
                proof {
                    if peak_idx > mid as int {
                        assert(mountain_arr.data@[mid as int] < mountain_arr.data@[mid as int + 1]);
                    }
                }
                right = mid;
            }
        }
        let peak = left;

        let mut lo: i32 = 0;
        let mut hi: i32 = peak + 1;
        while lo < hi
            invariant
                0 <= lo <= hi <= peak + 1,
                peak as int == peak_idx,
                Self::is_mountain(mountain_arr.data@, peak_idx),
                n == mountain_arr.data.len(),
                3 <= n <= 10_000,
                peak < n,
                forall |i: int| 0 <= i < n as int ==> 0 <= #[trigger] mountain_arr.data@[i] <= 1_000_000_000,
                forall |j: int| 0 <= j < lo as int ==> mountain_arr.data@[j] < target,
                hi as int <= peak as int ==> mountain_arr.data@[hi as int] >= target,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            if mountain_arr.get(mid) < target {
                proof {
                    assert forall |j: int| 0 <= j < mid as int + 1 implies mountain_arr.data@[j] < target by {
                        if j >= lo as int && j < mid as int {
                            assert(mountain_arr.data@[j] < mountain_arr.data@[mid as int]);
                        }
                    };
                }
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        if lo <= peak && mountain_arr.get(lo) == target {
            return lo;
        }

        proof {
            if lo as int <= peak as int {
                assert(mountain_arr.data@[lo as int] >= target);
            }
            assert forall |j: int| 0 <= j <= peak as int implies mountain_arr.data@[j] != target by {
                if j < lo as int {
                    assert(mountain_arr.data@[j] < target);
                } else if lo as int <= peak as int {
                    if j == lo as int {
                        assert(mountain_arr.data@[j] >= target && mountain_arr.data@[j] != target);
                    } else {
                        assert(mountain_arr.data@[lo as int] < mountain_arr.data@[j]);
                    }
                }
            };
        }

        lo = peak + 1;
        hi = n;
        while lo < hi
            invariant
                peak as int + 1 <= lo as int,
                lo <= hi,
                hi as int <= n as int,
                peak as int == peak_idx,
                Self::is_mountain(mountain_arr.data@, peak_idx),
                n == mountain_arr.data.len(),
                3 <= n <= 10_000,
                peak < n,
                forall |i: int| 0 <= i < n as int ==> 0 <= #[trigger] mountain_arr.data@[i] <= 1_000_000_000,
                forall |j: int| 0 <= j <= peak as int ==> mountain_arr.data@[j] != target,
                forall |j: int| peak as int + 1 <= j < lo as int ==> mountain_arr.data@[j] > target,
                hi < n ==> mountain_arr.data@[hi as int] <= target,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            if mountain_arr.get(mid) > target {
                proof {
                    assert forall |j: int| peak as int + 1 <= j < mid as int + 1 implies mountain_arr.data@[j] > target by {
                        if j >= lo as int && j < mid as int {
                            assert(mountain_arr.data@[j] > mountain_arr.data@[mid as int]);
                        }
                    };
                }
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        if lo < n && mountain_arr.get(lo) == target {
            proof {
                assert forall |j: int| 0 <= j < lo as int implies mountain_arr.data@[j] != target by {
                    if j > peak as int {
                        assert(mountain_arr.data@[j] > target);
                    }
                };
            }
            return lo;
        }

        proof {
            if lo < n {
                assert(mountain_arr.data@[lo as int] <= target);
                assert(mountain_arr.data@[lo as int] != target);
                assert forall |j: int| lo as int <= j < n as int implies mountain_arr.data@[j] != target by {
                    if j > lo as int {
                        assert(mountain_arr.data@[j] < mountain_arr.data@[lo as int]);
                    }
                };
            }
            assert forall |j: int| 0 <= j < n as int implies mountain_arr.data@[j] != target by {
                if j <= peak as int {
                } else if j < lo as int {
                    assert(mountain_arr.data@[j] > target);
                }
            };
        }

        -1
    }
}

}
