use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn token_prefix(bloom_day: Seq<i32>, day: int, k: int, i: int) -> int
        recommends
            0 <= i <= bloom_day.len(),
            k >= 1,
        decreases i,
    {
        if i <= 0 {
            0
        } else {
            let prev = Self::token_prefix(bloom_day, day, k, i - 1);
            if bloom_day[i - 1] as int <= day {
                prev + 1
            } else {
                (prev / k) * k
            }
        }
    }

    pub open spec fn bouquets_by_day_spec(bloom_day: Seq<i32>, day: int, k: int) -> int
        recommends
            k >= 1,
    {
        Self::token_prefix(bloom_day, day, k, bloom_day.len() as int) / k
    }

    pub open spec fn can_make(bloom_day: Seq<i32>, day: int, m: int, k: int) -> bool
        recommends
            m >= 1,
            k >= 1,
    {
        Self::bouquets_by_day_spec(bloom_day, day, k) >= m
    }

    pub open spec fn max_prefix(bloom_day: Seq<i32>, n: int) -> int
        recommends
            1 <= n <= bloom_day.len(),
        decreases n,
    {
        if n <= 1 {
            bloom_day[0] as int
        } else {
            let prev = Self::max_prefix(bloom_day, n - 1);
            let cur = bloom_day[n - 1] as int;
            if prev >= cur { prev } else { cur }
        }
    }

    pub open spec fn max_bloom(bloom_day: Seq<i32>) -> int
        recommends
            bloom_day.len() >= 1,
    {
        Self::max_prefix(bloom_day, bloom_day.len() as int)
    }

    proof fn lemma_cut_mono(k: int, x: int, y: int)
        requires
            k >= 1,
            x <= y,
        ensures
            (x / k) * k <= (y / k) * k,
    {
        assert((x / k) <= (y / k)) by (nonlinear_arith)
            requires k >= 1, x <= y
        {
        }
        assert((x / k) * k <= (y / k) * k) by (nonlinear_arith)
            requires k >= 1, (x / k) <= (y / k)
        {
        }
    }

    proof fn lemma_div_mono(k: int, x: int, y: int)
        requires
            k >= 1,
            x <= y,
        ensures
            x / k <= y / k,
    {
        assert((x / k) <= (y / k)) by (nonlinear_arith)
            requires k >= 1, x <= y
        {
        }
    }

    proof fn lemma_token_prefix_upper(bloom_day: Seq<i32>, day: int, k: int, i: int)
        requires
            0 <= i <= bloom_day.len(),
            k >= 1,
        ensures
            0 <= Self::token_prefix(bloom_day, day, k, i) <= i,
        decreases i,
    {
        if i > 0 {
            Self::lemma_token_prefix_upper(bloom_day, day, k, i - 1);
            let prev = Self::token_prefix(bloom_day, day, k, i - 1);
            if bloom_day[i - 1] as int <= day {
                assert(0 <= prev + 1 <= i) by (nonlinear_arith)
                    requires 0 <= prev <= i - 1
                {
                }
            } else {
                assert((prev / k) * k <= prev) by (nonlinear_arith)
                    requires k >= 1
                {
                }
                assert(0 <= (prev / k) * k <= i) by (nonlinear_arith)
                    requires 0 <= prev <= i, (prev / k) * k <= prev
                {
                }
            }
        }
    }

    proof fn lemma_token_prefix_mono(bloom_day: Seq<i32>, day1: int, day2: int, k: int, i: int)
        requires
            0 <= i <= bloom_day.len(),
            k >= 1,
            day1 <= day2,
        ensures
            Self::token_prefix(bloom_day, day1, k, i) <= Self::token_prefix(bloom_day, day2, k, i),
        decreases i,
    {
        if i > 0 {
            Self::lemma_token_prefix_mono(bloom_day, day1, day2, k, i - 1);
            let p1 = Self::token_prefix(bloom_day, day1, k, i - 1);
            let p2 = Self::token_prefix(bloom_day, day2, k, i - 1);
            let b1 = bloom_day[i - 1] as int <= day1;
            let b2 = bloom_day[i - 1] as int <= day2;
            if b1 {
                assert(b2);
            }
            if b1 && b2 {
                assert(p1 + 1 <= p2 + 1) by (nonlinear_arith)
                    requires p1 <= p2
                {
                }
            } else if !b1 && b2 {
                Self::lemma_cut_mono(k, p1, p2);
                assert((p1 / k) * k <= p1) by (nonlinear_arith)
                    requires k >= 1
                {
                }
                assert((p1 / k) * k <= p2 + 1) by (nonlinear_arith)
                    requires (p1 / k) * k <= p1, p1 <= p2
                {
                }
            } else {
                Self::lemma_cut_mono(k, p1, p2);
            }
        }
    }

    proof fn lemma_token_prefix_all_bloomed(bloom_day: Seq<i32>, day: int, k: int, i: int)
        requires
            0 <= i <= bloom_day.len(),
            k >= 1,
            forall |j: int| 0 <= j < i ==> bloom_day[j] as int <= day,
        ensures
            Self::token_prefix(bloom_day, day, k, i) == i,
        decreases i,
    {
        if i > 0 {
            Self::lemma_token_prefix_all_bloomed(bloom_day, day, k, i - 1);
            assert(bloom_day[i - 1] as int <= day);
            assert(Self::token_prefix(bloom_day, day, k, i)
                == Self::token_prefix(bloom_day, day, k, i - 1) + 1);
        }
    }

    proof fn lemma_can_make_mono(bloom_day: Seq<i32>, day1: int, day2: int, m: int, k: int)
        requires
            1 <= m,
            1 <= k,
            day1 <= day2,
            Self::can_make(bloom_day, day1, m, k),
        ensures
            Self::can_make(bloom_day, day2, m, k),
    {
        Self::lemma_token_prefix_mono(bloom_day, day1, day2, k, bloom_day.len() as int);
        Self::lemma_div_mono(k,
            Self::token_prefix(bloom_day, day1, k, bloom_day.len() as int),
            Self::token_prefix(bloom_day, day2, k, bloom_day.len() as int));
        assert(Self::bouquets_by_day_spec(bloom_day, day1, k)
            <= Self::bouquets_by_day_spec(bloom_day, day2, k));
    }

    proof fn lemma_max_prefix_upper(bloom_day: Seq<i32>, n: int, i: int)
        requires
            1 <= n <= bloom_day.len(),
            0 <= i < n,
        ensures
            bloom_day[i] as int <= Self::max_prefix(bloom_day, n),
        decreases n,
    {
        if n > 1 {
            if i < n - 1 {
                Self::lemma_max_prefix_upper(bloom_day, n - 1, i);
            }
        }
    }

    fn bouquets_by_day(bloom_day: &Vec<i32>, day: i32, k: i32) -> (res: i32)
        requires
            1 <= bloom_day.len() <= 100_000,
            forall |i: int| 0 <= i < bloom_day.len() ==> 1 <= #[trigger] bloom_day[i] <= 1_000_000_000,
            1 <= day <= 1_000_000_000,
            1 <= k <= bloom_day.len(),
        ensures
            res as int == Self::bouquets_by_day_spec(bloom_day@, day as int, k as int),
    {
        let mut tokens: i32 = 0;
        let mut i: usize = 0;
        while i < bloom_day.len()
            invariant
                0 <= i <= bloom_day.len(),
                1 <= bloom_day.len() <= 100_000,
                1 <= k <= bloom_day.len(),
                1 <= day <= 1_000_000_000,
                forall |j: int| 0 <= j < bloom_day.len() ==> 1 <= #[trigger] bloom_day@[j] <= 1_000_000_000,
                0 <= tokens as int <= i as int,
                tokens as int == Self::token_prefix(bloom_day@, day as int, k as int, i as int),
            decreases bloom_day.len() - i,
        {
            if bloom_day[i] <= day {
                proof {
                    assert(tokens as int + 1 <= i as int + 1) by (nonlinear_arith)
                        requires tokens as int <= i as int
                    {
                    }
                    assert(i as int + 1 <= 100_000) by (nonlinear_arith)
                        requires i < bloom_day.len(), bloom_day.len() <= 100_000
                    {
                    }
                    assert(tokens as int + 1 <= 100_000) by (nonlinear_arith)
                        requires tokens as int + 1 <= i as int + 1, i as int + 1 <= 100_000
                    {
                    }
                }
                tokens += 1;
                proof {
                    assert(Self::token_prefix(bloom_day@, day as int, k as int, (i + 1) as int)
                        == Self::token_prefix(bloom_day@, day as int, k as int, i as int) + 1);
                }
            } else {
                proof {
                    assert((tokens / k) <= tokens) by (nonlinear_arith)
                        requires 0 <= tokens as int, k as int >= 1
                    {
                    }
                    assert((tokens / k) * k <= tokens) by (nonlinear_arith)
                        requires 0 <= tokens as int, k as int >= 1
                    {
                    }
                    assert((tokens / k) * k <= 100_000) by (nonlinear_arith)
                        requires (tokens / k) * k <= tokens, tokens <= 100_000
                    {
                    }
                    assert((tokens as int / k as int) * k as int <= tokens as int) by (nonlinear_arith)
                        requires k as int >= 1
                    {
                    }
                }
                tokens = (tokens / k) * k;
                proof {
                    assert(Self::token_prefix(bloom_day@, day as int, k as int, (i + 1) as int)
                        == (Self::token_prefix(bloom_day@, day as int, k as int, i as int) / k as int) * k as int);
                }
            }
            i += 1;
        }
        proof {
            assert(tokens as int == Self::token_prefix(bloom_day@, day as int, k as int, bloom_day.len() as int));
            assert(0 <= tokens as int <= bloom_day.len() as int);
            assert(0 <= tokens / k <= 100_000) by (nonlinear_arith)
                requires
                    0 <= tokens as int,
                    k as int >= 1,
                    tokens as int <= 100_000
            {
            }
        }
        tokens / k
    }

    fn required_flowers(m: i32, k: i32) -> (need: u64)
        requires
            1 <= m <= 1_000_000,
            1 <= k <= 100_000,
        ensures
            need as int == (m as int) * (k as int),
    {
        let mut total: u64 = 0;
        let mut i: i32 = 0;
        while i < m
            invariant
                0 <= i <= m,
                1 <= m <= 1_000_000,
                1 <= k <= 100_000,
                total as int == (i as int) * (k as int),
            decreases m - i,
        {
            proof {
                assert((i as int + 1) * (k as int) <= (i as int + 1) * 100_000) by (nonlinear_arith)
                    requires i as int + 1 >= 0, k as int <= 100_000
                {
                }
                assert(total as int + k as int == (i as int + 1) * (k as int)) by (nonlinear_arith)
                    requires total as int == (i as int) * (k as int)
                {
                }
            }
            total = total + (k as u64);
            i += 1;
        }
        total
    }

    pub fn min_days(bloom_day: Vec<i32>, m: i32, k: i32) -> (res: i32)
        requires
            1 <= bloom_day.len() <= 100_000,
            forall |i: int| 0 <= i < bloom_day.len() ==> 1 <= #[trigger] bloom_day[i] <= 1_000_000_000,
            1 <= m <= 1_000_000,
            1 <= k <= bloom_day.len(),
        ensures
            (m as int) * (k as int) > bloom_day.len() ==> res == -1,
            (m as int) * (k as int) <= bloom_day.len() ==> (
                1 <= res <= Self::max_bloom(bloom_day@)
                && Self::can_make(bloom_day@, res as int, m as int, k as int)
                && forall |d: int| 1 <= d < res ==> !Self::can_make(bloom_day@, d, m as int, k as int)
            ),
    {
        let n = bloom_day.len();
        let need = Self::required_flowers(m, k);
        if need > n as u64 {
            proof {
                assert((m as int) * (k as int) > n as int) by (nonlinear_arith)
                    requires
                        need > n as u64,
                        need as int == (m as int) * (k as int)
                {
                }
            }
            return -1;
        }

        let mut max_day = bloom_day[0];
        let mut i: usize = 1;
        while i < n
            invariant
                n == bloom_day.len(),
                1 <= n <= 100_000,
                1 <= i <= n,
                1 <= max_day <= 1_000_000_000,
                forall |j: int| 0 <= j < n ==> 1 <= #[trigger] bloom_day@[j] <= 1_000_000_000,
                forall |j: int| 0 <= j < i ==> bloom_day@[j] <= max_day,
                exists |j: int| 0 <= j < i && bloom_day@[j] == max_day,
            decreases n - i,
        {
            if bloom_day[i] > max_day {
                max_day = bloom_day[i];
            }
            i += 1;
        }

        proof {
            assert(forall |j: int| 0 <= j < n ==> bloom_day@[j] as int <= max_day as int) by {
                assert(bloom_day[0] <= max_day);
                assert forall |j: int| 0 <= j < n implies bloom_day@[j] as int <= max_day as int by {
                    if j == 0 {
                    } else {
                    }
                }
            };
            assert(max_day as int <= Self::max_bloom(bloom_day@)) by {
                let idx = choose |idx: int| 0 <= idx < n && bloom_day@[idx] == max_day;
                Self::lemma_max_prefix_upper(bloom_day@, n as int, idx);
            }
        }

        let mut left: i32 = 1;
        let mut right: i32 = max_day;

        proof {
            Self::lemma_token_prefix_upper(bloom_day@, right as int, k as int, n as int);
            assert(right == max_day);
            assert(Self::token_prefix(bloom_day@, right as int, k as int, n as int) == n as int) by {
                assert forall |j: int| 0 <= j < n implies bloom_day@[j] as int <= right as int by {
                }
                Self::lemma_token_prefix_all_bloomed(bloom_day@, right as int, k as int, n as int);
            }
            assert(Self::bouquets_by_day_spec(bloom_day@, right as int, k as int) == (n as int) / (k as int));
            assert((m as int) * (k as int) <= n as int) by (nonlinear_arith)
                requires
                    need <= n as u64,
                    need as int == (m as int) * (k as int)
            {
            }
            assert((n as int) / (k as int) >= m as int) by (nonlinear_arith)
                requires
                    (m as int) * (k as int) <= n as int,
                    k as int >= 1
            {
            }
            assert(Self::can_make(bloom_day@, right as int, m as int, k as int));
        }

        while left < right
            invariant
                n == bloom_day.len(),
                1 <= bloom_day.len() <= 100_000,
                1 <= max_day <= 1_000_000_000,
                1 <= left <= right <= max_day,
                max_day as int <= Self::max_bloom(bloom_day@),
                1 <= k <= bloom_day.len(),
                1 <= m <= 1_000_000,
                forall |j: int| 0 <= j < n ==> 1 <= #[trigger] bloom_day@[j] <= 1_000_000_000,
                Self::can_make(bloom_day@, right as int, m as int, k as int),
                forall |d: int| 1 <= d < left ==> !Self::can_make(bloom_day@, d, m as int, k as int),
            decreases right - left,
        {
            let mid = left + (right - left) / 2;
            proof {
                assert(1 <= mid <= max_day) by (nonlinear_arith)
                    requires 1 <= left <= right <= max_day, left < right, mid == left + (right - left) / 2
                {
                }
            }
            let made = Self::bouquets_by_day(&bloom_day, mid, k);
            if made >= m {
                proof {
                    assert(Self::bouquets_by_day_spec(bloom_day@, mid as int, k as int)
                        == made as int);
                    assert(Self::can_make(bloom_day@, mid as int, m as int, k as int));
                }
                right = mid;
            } else {
                proof {
                    assert(Self::bouquets_by_day_spec(bloom_day@, mid as int, k as int)
                        == made as int);
                    assert(Self::bouquets_by_day_spec(bloom_day@, mid as int, k as int)
                        < m as int);
                    assert(!Self::can_make(bloom_day@, mid as int, m as int, k as int));
                    assert forall |d: int| 1 <= d < mid + 1 implies !Self::can_make(bloom_day@, d, m as int, k as int) by {
                        if d < left {
                        } else {
                            assert(d <= mid as int) by (nonlinear_arith)
                                requires d < mid as int + 1
                            {
                            }
                            if Self::can_make(bloom_day@, d, m as int, k as int) {
                                Self::lemma_can_make_mono(bloom_day@, d, mid as int, m as int, k as int);
                                assert(false);
                            }
                        }
                    }
                }
                left = mid + 1;
            }
        }

        left
    }
}

}
