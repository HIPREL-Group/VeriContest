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
        while c < 24
            invariant
                0 <= c <= 24,
                cnt.len() == c,
                forall |r: int| 0 <= r < cnt.len() ==> #[trigger] cnt[r] == 0,
            decreases 24 - c,
        {
            cnt.push(0);
            c += 1;
        }
        let mut ans = 0i64;
        let mut i = 0usize;
        while i < hours.len()
            invariant
                1 <= hours.len() <= 500000,
                cnt.len() == 24,
                0 <= i <= hours.len(),
                0 <= ans,
                ans as int <= (i as int * (i as int - 1)) / 2,
                forall |j: int| 0 <= j < hours.len() ==> 1 <= #[trigger] hours[j] <= 1_000_000_000,
                forall |r: int| 0 <= r < 24 ==> 0 <= #[trigger] cnt[r],
                forall |r: int| 0 <= r < 24 ==> #[trigger] cnt[r] <= i as i64,
                ans as int == Self::pair_count_prefix(hours@, i as int),
                forall |r: int| 0 <= r < 24 ==> #[trigger] cnt[r] as int == Self::count_rem_prefix(hours@, i as int, r),
            decreases hours.len() - i,
        {
            let rem = (hours[i] % 24) as usize;
            let need = (24usize - rem) % 24usize;
            assert(0 <= rem < 24);
            assert(0 <= need < 24);
            assert(Self::rem24(hours@[i as int] as int) == rem as int);
            assert((24 - Self::rem24(hours@[i as int] as int)) % 24 == need as int);
            assert(Self::pair_count_prefix(hours@, (i + 1) as int)
                == Self::pair_count_prefix(hours@, i as int)
                    + Self::count_rem_prefix(hours@, i as int, need as int));
            assert(cnt[need as int] <= i as i64);
            proof {
                assert(ans as int + cnt[need as int] as int <= ((i as int + 1) * i as int) / 2) by (nonlinear_arith)
                    requires
                        ans as int <= (i as int * (i as int - 1)) / 2,
                        cnt[need as int] as int <= i as int,
                { }
                assert(i as int <= 500000);
                assert(ans as int <= 125_000_000_000) by (nonlinear_arith)
                    requires
                        ans as int <= (i as int * (i as int - 1)) / 2,
                        i as int <= 500000,
                { }
            }
            assert(ans <= 125_000_000_000i64);
            assert(cnt[need as int] <= 500_000i64);
            assert(ans + cnt[need as int] <= 125_000_500_000i64);
            assert(ans + cnt[need as int] <= i64::MAX);
            let add = cnt[need];
            assert(ans.checked_add(add).is_some());
            ans = ans.checked_add(cnt[need]).unwrap_or(ans);
            assert(ans as int == Self::pair_count_prefix(hours@, (i + 1) as int));
            cnt.set(rem, cnt[rem].checked_add(1).unwrap_or(cnt[rem]));
            assert(cnt[rem as int] as int == Self::count_rem_prefix(hours@, (i + 1) as int, rem as int));
            assert forall |r: int| 0 <= r < 24 && r != rem as int
                implies #[trigger] cnt[r] as int == Self::count_rem_prefix(hours@, (i + 1) as int, r) by {
                assert(Self::count_rem_prefix(hours@, (i + 1) as int, r)
                    == Self::count_rem_prefix(hours@, i as int, r)
                        + if Self::rem24(hours@[i as int] as int) == r { 1int } else { 0int });
                assert(Self::rem24(hours@[i as int] as int) == rem as int);
                assert(Self::rem24(hours@[i as int] as int) != r);
            };
            assert(cnt[rem as int] <= i as i64 + 1);
            assert forall |r: int| 0 <= r < 24 && r != rem as int implies #[trigger] cnt[r] <= i as i64 + 1 by {
                assert(cnt[r] <= i as i64);
            };
            i += 1;
        }
        ans
    }
}

}
