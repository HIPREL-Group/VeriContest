use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_count_prefix(a: Seq<i32>, v: int, i: int) -> int
        decreases i
    {
        if i <= 0 {
            0
        } else {
            Self::spec_count_prefix(a, v, i - 1) + if a[i - 1] as int == v { 1int } else { 0int }
        }
    }

    pub open spec fn spec_count(a: Seq<i32>, v: int) -> int {
        Self::spec_count_prefix(a, v, a.len() as int)
    }

    pub open spec fn spec_max2(x: int, y: int) -> int {
        if x >= y { x } else { y }
    }

    pub open spec fn spec_max_freq_upto(a: Seq<i32>, upto: int) -> int
        decreases upto
    {
        if upto <= 0 {
            0
        } else {
            Self::spec_max2(Self::spec_max_freq_upto(a, upto - 1), Self::spec_count(a, upto))
        }
    }

    pub open spec fn spec_max_freq(a: Seq<i32>) -> int {
        Self::spec_max_freq_upto(a, a.len() as int)
    }

    pub open spec fn spec_min_remaining(a: Seq<i32>) -> int {
        let n = a.len() as int;
        let m = Self::spec_max_freq(a);
        if 2 * m > n { 2 * m - n } else { n % 2 }
    }

    pub fn min_remaining_after_epic_transformation(a: Vec<i32>) -> (res: i32)
        requires
            1 <= a.len() <= 200000,
            forall|j: int| 0 <= j < a.len() as int ==> 1 <= #[trigger] a[j] <= a.len(),
        ensures
            res as int == Self::spec_min_remaining(a@),
    {
        let n: usize = a.len();
        let mut cnt: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= n
            invariant
                n == a.len(),
                1 <= n <= 200000,
                0 <= k <= n + 1,
                cnt.len() == k,
                forall|j: int| 0 <= j < k as int ==> cnt[j] == 0,
            decreases n + 1 - k,
        {
            cnt.push(0);
            k = k + 1;
        }

        let mut i: usize = 0;
        while i < n
            invariant
                n == a.len(),
                1 <= n <= 200000,
                cnt.len() == n + 1,
                0 <= i <= n,
                cnt[0] == 0,
                forall|j: int| 0 <= j < a.len() as int ==> 1 <= #[trigger] a[j] <= a.len(),
                forall|v: int| 1 <= v <= n as int ==> cnt[v] as int == Self::spec_count_prefix(a@, v, i as int),
                forall|v: int| 1 <= v <= n as int ==> 0 <= #[trigger] cnt[v] <= i as i32,
            decreases n - i,
        {
            let v: usize = a[i] as usize;
            assert(0 <= cnt[v as int] <= i as i32);
            assert(i <= 199999);
            assert(cnt[v as int] + 1 <= 200000);
            let ghost old_cnt = cnt@;
            cnt.set(v, cnt[v] + 1);
            proof {
                assert(v as int == a[i as int] as int);
                assert(1 <= v as int <= n as int);
                assert forall|vv: int| 1 <= vv <= n as int implies cnt[vv] as int == Self::spec_count_prefix(a@, vv, i as int + 1) by {
                    if vv == v as int {
                        assert(cnt[vv] == old_cnt[vv] + 1);
                        assert(old_cnt[vv] as int == Self::spec_count_prefix(a@, vv, i as int));
                        assert(a[i as int] as int == vv);
                    } else {
                        assert(cnt[vv] == old_cnt[vv]);
                        assert(old_cnt[vv] as int == Self::spec_count_prefix(a@, vv, i as int));
                        assert(a[i as int] as int != vv);
                    }
                };
                assert forall|vv: int| 1 <= vv <= n as int implies 0 <= #[trigger] cnt[vv] <= i as i32 + 1 by {
                    if vv == v as int {
                        assert(0 <= old_cnt[vv] <= i as i32);
                        assert(cnt[vv] == old_cnt[vv] + 1);
                    } else {
                        assert(cnt[vv] == old_cnt[vv]);
                    }
                };
                assert(cnt[0] == 0);
            }
            i = i + 1;
        }

        let mut mx: i32 = 0;
        let mut p: usize = 1;
        while p <= n
            invariant
                n == a.len(),
                1 <= n <= 200000,
                cnt.len() == n + 1,
                cnt[0] == 0,
                forall|j: int| 0 <= j < a.len() as int ==> 1 <= #[trigger] a[j] <= a.len(),
                forall|v: int| 1 <= v <= n as int ==> cnt[v] as int == Self::spec_count(a@, v),
                forall|v: int| 1 <= v <= n as int ==> 0 <= #[trigger] cnt[v] <= n as i32,
                1 <= p <= n + 1,
                0 <= mx <= n as i32,
                mx as int == Self::spec_max_freq_upto(a@, p as int - 1),
            decreases n + 1 - p,
        {
            if cnt[p] > mx {
                assert(0 <= cnt[p as int] <= n as i32);
                mx = cnt[p];
            }
            proof {
                assert(cnt[p as int] as int == Self::spec_count(a@, p as int));
                assert(mx as int == Self::spec_max2(Self::spec_max_freq_upto(a@, p as int - 1), Self::spec_count(a@, p as int)));
                assert(Self::spec_max_freq_upto(a@, p as int) == Self::spec_max2(Self::spec_max_freq_upto(a@, p as int - 1), Self::spec_count(a@, p as int)));
            }
            p = p + 1;
        }

        let n_i32: i32 = n as i32;
        let two_mx: i32 = mx + mx;
        if two_mx > n_i32 {
            proof {
                assert(mx as int == Self::spec_max_freq_upto(a@, n as int));
                assert(Self::spec_max_freq(a@) == Self::spec_max_freq_upto(a@, n as int));
                assert(two_mx as int == 2 * Self::spec_max_freq(a@));
                assert(n_i32 as int == a.len() as int);
                assert(2 * Self::spec_max_freq(a@) > a.len() as int);
                assert(Self::spec_min_remaining(a@) == 2 * Self::spec_max_freq(a@) - a.len() as int);
            }
            two_mx - n_i32
        } else {
            proof {
                assert(mx as int == Self::spec_max_freq_upto(a@, n as int));
                assert(Self::spec_max_freq(a@) == Self::spec_max_freq_upto(a@, n as int));
                assert(two_mx as int == 2 * Self::spec_max_freq(a@));
                assert(n_i32 as int == a.len() as int);
                assert(!(2 * Self::spec_max_freq(a@) > a.len() as int));
                assert(Self::spec_min_remaining(a@) == a.len() as int % 2);
            }
            n_i32 % 2
        }
    }
}

}
