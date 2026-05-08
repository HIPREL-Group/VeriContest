use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn rem24(v: int) -> int {
        v % 24
    }

    pub open spec fn count_rem_prefix(hours: Seq<i32>, end: int, r: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_rem_prefix(hours, end - 1, r)
                + if Self::rem24(hours[end - 1] as int) == r { 1int } else { 0int }
        }
    }

    pub open spec fn pair_count_prefix(hours: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            let rem = Self::rem24(hours[end - 1] as int);
            let need = (24 - rem) % 24;
            Self::pair_count_prefix(hours, end - 1) + Self::count_rem_prefix(hours, end - 1, need)
        }
    }

    pub open spec fn count_complete_day_pairs_spec(hours: Seq<i32>, result: int) -> bool {
        &&& 1 <= hours.len() <= 500000
        &&& forall |i: int| 0 <= i < hours.len() ==> 1 <= #[trigger] hours[i] <= 1_000_000_000
        &&& result == Self::pair_count_prefix(hours, hours.len() as int)
    }

    pub fn count_complete_day_pairs(hours: Vec<i32>) -> (result: i64)
        requires
            1 <= hours.len() <= 500000,
            forall |i: int| 0 <= i < hours.len() ==> 1 <= #[trigger] hours[i] <= 1_000_000_000,
        ensures
            Self::count_complete_day_pairs_spec(hours@, result as int),
    {
        let mut cnt: Vec<i64> = Vec::new();
        let mut c = 0usize;
        while c < 24 {
            cnt.push(0);
            c += 1;
        }
        let mut ans = 0i64;
        let mut i = 0usize;
        while i < hours.len() {
            let rem = (hours[i] % 24) as usize;
            let need = (24usize - rem) % 24usize;
            ans = ans.checked_add(cnt[need]).unwrap_or(ans);
            cnt.set(rem, cnt[rem].checked_add(1).unwrap_or(cnt[rem]));
            i += 1;
        }
        ans
    }
}

}
