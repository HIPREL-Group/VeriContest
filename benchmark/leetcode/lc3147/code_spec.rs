use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn checked_add_i32(a: int, b: int) -> int {
        let s = a + b;
        if s < -2_147_483_648 || s > 2_147_483_647 { 0 } else { s }
    }

    pub open spec fn path_sum_from(energy: Seq<i32>, k: int, i: int) -> int
        decreases energy.len() - i,
    {
        if !(0 <= i < energy.len()) {
            0
        } else if k <= 0 || i + k >= energy.len() {
            energy[i] as int
        } else {
            Self::checked_add_i32(energy[i] as int, Self::path_sum_from(energy, k, i + k))
        }
    }

    pub open spec fn maximum_energy_spec(energy: Seq<i32>, k: int, result: int) -> bool {
        &&& 1 <= energy.len() <= 100_000
        &&& 1 <= k <= energy.len() - 1
        &&& exists |i: int| 0 <= i < energy.len() && result == Self::path_sum_from(energy, k, i)
        &&& forall |i: int| 0 <= i < energy.len() ==> result >= #[trigger] Self::path_sum_from(energy, k, i)
    }

    pub fn maximum_energy(energy: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= energy.len() <= 100_000,
            forall |i: int| 0 <= i < energy.len() ==> -1000 <= #[trigger] energy[i] <= 1000,
            1 <= k <= energy.len() - 1,
        ensures
            Self::maximum_energy_spec(energy@, k as int, result as int),
    {
        let n = energy.len();
        let ku = k as usize;
        let mut arr = energy.clone();

        let mut idx = n;
        while idx > 0 {
            idx -= 1;
            if idx + ku < n {
                let sum = arr[idx] as i64 + arr[idx + ku] as i64;
                let v = if sum < i32::MIN as i64 || sum > i32::MAX as i64 {
                    0
                } else {
                    sum as i32
                };
                arr.set(idx, v);
            }
        }

        let mut ans = arr[0];
        let mut j = 1usize;
        while j < n {
            if arr[j] > ans {
                ans = arr[j];
            }
            j += 1;
        }
        ans
    }
}

}
