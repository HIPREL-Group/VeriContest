use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn imin(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn sub_or(nums: Seq<i32>, start: int, end: int) -> i32
        decreases end - start,
    {
        if end <= start {
            0i32
        } else {
            Self::sub_or(nums, start, end - 1) | nums[end - 1]
        }
    }

    pub open spec fn min_len_start_upto(nums: Seq<i32>, k: i32, start: int, upto: int) -> int
        decreases upto - start,
    {
        if upto <= start {
            nums.len() as int + 1
        } else {
            let prev = Self::min_len_start_upto(nums, k, start, upto - 1);
            let cand = if Self::sub_or(nums, start, upto) >= k {
                upto - start
            } else {
                nums.len() as int + 1
            };
            Self::imin(prev, cand)
        }
    }

    pub open spec fn min_len_prefix(nums: Seq<i32>, k: i32, processed: int) -> int
        decreases processed,
    {
        if processed <= 0 {
            nums.len() as int + 1
        } else {
            let prev = Self::min_len_prefix(nums, k, processed - 1);
            let cur = Self::min_len_start_upto(nums, k, processed - 1, nums.len() as int);
            Self::imin(prev, cur)
        }
    }

    pub open spec fn minimum_subarray_length_spec(nums: Seq<i32>, k: i32) -> int {
        let best = Self::min_len_prefix(nums, k, nums.len() as int);
        if best <= nums.len() as int { best } else { -1 }
    }
}

pub open spec fn bit_set(x: i32, b: u32) -> bool {
    (x >> b) & 1 == 1
}

pub open spec fn low_mask(x: i32, upto: u32) -> i32 {
    x & (((1i32 << upto) - 1) as i32)
}

proof fn lemma_mask_step(x: i32, upto: u32)
    requires 0 <= x, upto < 30,
    ensures low_mask(x, (upto + 1) as u32) == (low_mask(x, upto) | (if bit_set(x, upto) { 1i32 << upto } else { 0i32 })),
{
    assert(low_mask(x, (upto + 1) as u32) == (low_mask(x, upto) | (if bit_set(x, upto) { 1i32 << upto } else { 0i32 }))) by (bit_vector)
        requires upto < 30;
}

proof fn lemma_same_bits_upto_eq(x: i32, y: i32, upto: u32)
    requires
        0 <= x, 0 <= y,
        forall |b: u32| b < upto ==> bit_set(x, b) == bit_set(y, b),
        upto <= 30,
    ensures low_mask(x, upto) == low_mask(y, upto),
    decreases upto,
{
    if upto > 0 {
        let prev: u32 = (upto - 1) as u32;
        lemma_same_bits_upto_eq(x, y, prev);
        lemma_mask_step(x, prev);
        lemma_mask_step(y, prev);
        assert(bit_set(x, prev) == bit_set(y, prev));
        assert((prev + 1) as u32 == upto);
    } else {
        assert(low_mask(x, 0) == 0) by (bit_vector);
        assert(low_mask(y, 0) == 0) by (bit_vector);
    }
}

proof fn lemma_low_mask_full(x: i32)
    requires 0 <= x < 1073741824i32,
    ensures low_mask(x, 30) == x,
{
    assert(low_mask(x, 30) == x) by (bit_vector)
        requires 0 <= x < 1073741824i32;
}

proof fn lemma_eq_from_same_bits(x: i32, y: i32)
    requires
        0 <= x < 1073741824i32, 0 <= y < 1073741824i32,
        forall |b: u32| b < 30 ==> bit_set(x, b) == bit_set(y, b),
    ensures x == y,
{
    lemma_same_bits_upto_eq(x, y, 30);
    lemma_low_mask_full(x);
    lemma_low_mask_full(y);
}

proof fn lemma_or_ge(x: i32, y: i32)
    requires 0 <= x, 0 <= y,
    ensures (x | y) >= x, (x | y) >= y, (x | y) >= 0,
{
    assert((x | y) >= x && (x | y) >= y && (x | y) >= 0) by (bit_vector)
        requires x >= 0, y >= 0;
}

proof fn lemma_or_bit(a: i32, c: i32, b: u32)
    ensures bit_set(a | c, b) == (bit_set(a, b) || bit_set(c, b)),
{
    assert(bit_set(a | c, b) == (bit_set(a, b) || bit_set(c, b))) by (bit_vector);
}

proof fn lemma_or_bound(x: i32, y: i32)
    requires 0 <= x < 1073741824i32, 0 <= y < 1073741824i32,
    ensures 0 <= (x | y) < 1073741824i32,
{
    assert(0 <= (x | y) && (x | y) < 1073741824i32) by (bit_vector)
        requires 0 <= x < 1073741824i32, 0 <= y < 1073741824i32;
}

proof fn lemma_or_zero(x: i32)
    requires 0 <= x,
    ensures (x | 0i32) == x,
{
    assert((x | 0i32) == x) by (bit_vector)
        requires 0 <= x;
}

proof fn lemma_or_assoc(a: i32, b: i32, c: i32)
    ensures (a | b | c) == (a | (b | c)),
{
    assert((a | b | c) == (a | (b | c))) by (bit_vector);
}

proof fn lemma_sub_or_bound(nums: Seq<i32>, start: int, end: int)
    requires
        0 <= start <= end <= nums.len(),
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < 1073741824i32,
    ensures 0 <= Solution::sub_or(nums, start, end) < 1073741824i32,
    decreases end - start,
{
    if end > start {
        lemma_sub_or_bound(nums, start, end - 1);
        lemma_or_bound(Solution::sub_or(nums, start, end - 1), nums[end - 1]);
    }
}

pub open spec fn count_bit(nums: Seq<i32>, start: int, end: int, b: u32) -> int
    decreases end - start,
{
    if end <= start {
        0
    } else {
        count_bit(nums, start, end - 1, b) + (if bit_set(nums[end - 1], b) { 1int } else { 0int })
    }
}

proof fn lemma_count_bit_nonneg(nums: Seq<i32>, start: int, end: int, b: u32)
    requires 0 <= start <= end,
    ensures count_bit(nums, start, end, b) >= 0,
    decreases end - start,
{
    if end > start {
        lemma_count_bit_nonneg(nums, start, end - 1, b);
    }
}

proof fn lemma_sub_or_bit_char(nums: Seq<i32>, start: int, end: int, b: u32)
    requires 0 <= start <= end <= nums.len(),
    ensures bit_set(Solution::sub_or(nums, start, end), b) == (count_bit(nums, start, end, b) > 0),
    decreases end - start,
{
    if end > start {
        lemma_sub_or_bit_char(nums, start, end - 1, b);
        lemma_or_bit(Solution::sub_or(nums, start, end - 1), nums[end - 1], b);
        lemma_count_bit_nonneg(nums, start, end - 1, b);
    } else {
        assert(bit_set(0i32, b) == false) by (bit_vector);
    }
}

proof fn lemma_sub_or_split(nums: Seq<i32>, lo: int, mid: int, hi: int)
    requires 0 <= lo <= mid <= hi <= nums.len(),
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < 1073741824i32,
    ensures Solution::sub_or(nums, lo, hi) == (Solution::sub_or(nums, lo, mid) | Solution::sub_or(nums, mid, hi)),
    decreases hi - mid,
{
    if hi > mid {
        lemma_sub_or_split(nums, lo, mid, hi - 1);
        lemma_or_assoc(Solution::sub_or(nums, lo, mid), Solution::sub_or(nums, mid, hi - 1), nums[hi - 1]);
    } else {
        assert(Solution::sub_or(nums, mid, hi) == 0i32);
        lemma_sub_or_bound(nums, lo, mid);
        lemma_or_zero(Solution::sub_or(nums, lo, mid));
    }
}

proof fn lemma_sub_or_mono_left(nums: Seq<i32>, lo: int, mid: int, hi: int)
    requires 0 <= lo <= mid <= hi <= nums.len(),
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < 1073741824i32,
    ensures Solution::sub_or(nums, mid, hi) <= Solution::sub_or(nums, lo, hi),
{
    lemma_sub_or_split(nums, lo, mid, hi);
    lemma_sub_or_bound(nums, lo, mid);
    lemma_sub_or_bound(nums, mid, hi);
    lemma_or_ge(Solution::sub_or(nums, lo, mid), Solution::sub_or(nums, mid, hi));
}

proof fn lemma_sub_or_mono_right(nums: Seq<i32>, lo: int, mid: int, hi: int)
    requires 0 <= lo <= mid <= hi <= nums.len(),
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < 1073741824i32,
    ensures Solution::sub_or(nums, lo, mid) <= Solution::sub_or(nums, lo, hi),
{
    lemma_sub_or_split(nums, lo, mid, hi);
    lemma_sub_or_bound(nums, lo, mid);
    lemma_sub_or_bound(nums, mid, hi);
    lemma_or_ge(Solution::sub_or(nums, lo, mid), Solution::sub_or(nums, mid, hi));
}

proof fn lemma_start_upto_all_invalid(nums: Seq<i32>, k: i32, start: int, upto: int)
    requires
        0 <= start <= upto <= nums.len(),
        forall |e: int| start < e <= upto ==> Solution::sub_or(nums, start, e) < k,
    ensures Solution::min_len_start_upto(nums, k, start, upto) == nums.len() as int + 1,
    decreases upto - start,
{
    if upto > start {
        lemma_start_upto_all_invalid(nums, k, start, upto - 1);
    }
}

proof fn lemma_start_upto_first_hit(nums: Seq<i32>, k: i32, start: int, r: int, upto: int)
    requires
        0 <= start < r <= upto <= nums.len(),
        forall |e: int| start < e < r ==> Solution::sub_or(nums, start, e) < k,
        Solution::sub_or(nums, start, r) >= k,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < 1073741824i32,
    ensures Solution::min_len_start_upto(nums, k, start, upto) == r - start,
    decreases upto - r,
{
    lemma_start_upto_all_invalid(nums, k, start, r - 1);
    if upto == r {
    } else {
        lemma_start_upto_first_hit(nums, k, start, r, upto - 1);
        lemma_sub_or_mono_right(nums, start, r, upto);
    }
}

pub open spec fn cnt_bits_value(cnt: Seq<int>, upto: int) -> i32
    decreases upto,
{
    if upto <= 0 {
        0i32
    } else {
        let prev = cnt_bits_value(cnt, upto - 1);
        if cnt[upto - 1] > 0 { prev | (1i32 << ((upto - 1) as u32)) } else { prev }
    }
}

proof fn lemma_bit_of_pow2(c: u32, b: u32)
    requires c < 30, b < 30,
    ensures bit_set(1i32 << c, b) == (b == c),
{
    assert(bit_set(1i32 << c, b) == (b == c)) by (bit_vector)
        requires c < 30, b < 30;
}

proof fn lemma_cnt_bits_value_char(cnt: Seq<int>, upto: int, b: u32)
    requires 0 <= upto <= 30, b < 30,
    ensures bit_set(cnt_bits_value(cnt, upto), b) == (b < upto && cnt[b as int] > 0),
    decreases upto,
{
    if upto > 0 {
        lemma_cnt_bits_value_char(cnt, upto - 1, b);
        let prev = cnt_bits_value(cnt, upto - 1);
        let bit_c: u32 = (upto - 1) as u32;
        if cnt[upto - 1] > 0 {
            lemma_or_bit(prev, 1i32 << bit_c, b);
            lemma_bit_of_pow2(bit_c, b);
        }
    } else {
        assert(bit_set(0i32, b) == false) by (bit_vector);
    }
}

proof fn lemma_cnt_bits_value_bound(cnt: Seq<int>, upto: int)
    requires 0 <= upto <= 30,
    ensures 0 <= cnt_bits_value(cnt, upto) < 1073741824i32,
    decreases upto,
{
    if upto > 0 {
        lemma_cnt_bits_value_bound(cnt, upto - 1);
        let prev = cnt_bits_value(cnt, upto - 1);
        let bit_c: u32 = (upto - 1) as u32;
        assert(0 <= prev && 0 <= (1i32 << bit_c) < 1073741824i32) by (bit_vector)
            requires 0 <= prev < 1073741824i32, bit_c < 30;
        lemma_or_bound(prev, 1i32 << bit_c);
        lemma_or_zero(prev);
    }
}

proof fn lemma_cnt_bits_value_matches_sub_or(nums: Seq<i32>, start: int, end: int, cnt: Seq<int>)
    requires
        0 <= start <= end <= nums.len(),
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < 1073741824i32,
        cnt.len() == 30,
        forall |b: int| 0 <= b < 30 ==> cnt[b] == count_bit(nums, start, end, b as u32),
    ensures cnt_bits_value(cnt, 30) == Solution::sub_or(nums, start, end),
{
    lemma_sub_or_bound(nums, start, end);
    lemma_cnt_bits_value_bound(cnt, 30);
    assert forall |b: u32| b < 30 implies
        bit_set(cnt_bits_value(cnt, 30), b) == bit_set(Solution::sub_or(nums, start, end), b) by {
        lemma_cnt_bits_value_char(cnt, 30, b);
        lemma_sub_or_bit_char(nums, start, end, b);
    };
    lemma_eq_from_same_bits(cnt_bits_value(cnt, 30), Solution::sub_or(nums, start, end));
}

proof fn lemma_count_bit_start_step(nums: Seq<i32>, start: int, end: int, b: u32)
    requires 0 <= start < end <= nums.len(),
    ensures
        count_bit(nums, start, end, b)
            == count_bit(nums, start + 1, end, b) + (if bit_set(nums[start], b) { 1int } else { 0int }),
    decreases end - start,
{
    if end == start + 1 {
        assert(count_bit(nums, start, start, b) == 0);
        assert(count_bit(nums, start + 1, start + 1, b) == 0);
    } else {
        lemma_count_bit_start_step(nums, start, end - 1, b);
    }
}

fn bit_set_exec(x: i32, b: u32) -> (result: bool)
    requires 0 <= x, b < 30,
    ensures result == bit_set(x, b),
{
    (x >> b) & 1 == 1
}

proof fn lemma_count_bit_bound(nums: Seq<i32>, start: int, end: int, b: u32)
    requires 0 <= start <= end,
    ensures 0 <= count_bit(nums, start, end, b) <= end - start,
    decreases end - start,
{
    if end > start {
        lemma_count_bit_bound(nums, start, end - 1, b);
    }
}

proof fn lemma_min_len_prefix_bound(nums: Seq<i32>, k: i32, processed: int)
    requires 0 <= processed <= nums.len(),
    ensures Solution::min_len_prefix(nums, k, processed) <= nums.len() as int + 1,
    decreases processed,
{
    if processed > 0 {
        lemma_min_len_prefix_bound(nums, k, processed - 1);
    }
}

impl Solution {
    pub fn minimum_subarray_length(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 200000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
            0 <= k <= 1_000_000_000,
        ensures
            result as int == Self::minimum_subarray_length_spec(nums@, k),
    {
        let n = nums.len();

        assert(forall |i: int| 0 <= i < n ==> 0 <= #[trigger] nums@[i] < 1073741824i32) by {
            assert forall |i: int| 0 <= i < n implies 0 <= #[trigger] nums@[i] < 1073741824i32 by {
            }
        };

        let mut cnt: Vec<i32> = Vec::new();
        let mut bi: usize = 0;
        while bi < 30
            invariant
                cnt.len() == bi,
                bi <= 30,
                forall |bb: int| 0 <= bb < bi ==> cnt[bb] == 0,
            decreases 30 - bi,
        {
            cnt.push(0);
            bi += 1;
        }

        let mut l: usize = 0;
        let mut r: usize = 0;
        let mut window_or: i32 = 0;
        let mut best: i32 = (n as i32) + 1;

        assert(Solution::min_len_prefix(nums@, k, 0) == n as int + 1);
        assert(Solution::sub_or(nums@, 0, 0) == 0i32);
        assert forall |b: int| 0 <= b < 30 implies cnt[b] as int == count_bit(nums@, 0, 0, b as u32) by {
        }

        while l < n
            invariant
                n == nums.len(),
                    n <= 200000,
                0 <= l <= r <= n,
                cnt.len() == 30,
                forall |b: int| 0 <= b < 30 ==> cnt[b] as int == count_bit(nums@, l as int, r as int, b as u32),
                forall |b: int| 0 <= b < 30 ==> 0 <= #[trigger] cnt[b] as int <= n as int,
                window_or == Solution::sub_or(nums@, l as int, r as int),
                best as int == Solution::min_len_prefix(nums@, k, l as int),
                forall |i: int| 0 <= i < n ==> 0 <= #[trigger] nums@[i] < 1073741824i32,
                forall |e: int| l < e < r as int ==> Solution::sub_or(nums@, l as int, e) < k,
            decreases n - l,
        {
            while r < n && !(r > l && window_or >= k)
                invariant
                    n == nums.len(),
                    n <= 200000,
                    l <= r <= n,
                    cnt.len() == 30,
                    forall |b: int| 0 <= b < 30 ==> cnt[b] as int == count_bit(nums@, l as int, r as int, b as u32),
                    forall |b: int| 0 <= b < 30 ==> 0 <= #[trigger] cnt[b] as int <= n as int,
                    window_or == Solution::sub_or(nums@, l as int, r as int),
                    forall |i: int| 0 <= i < n ==> 0 <= #[trigger] nums@[i] < 1073741824i32,
                    forall |e: int| l < e < r as int ==> Solution::sub_or(nums@, l as int, e) < k,
                decreases n - r,
            {
                if r > l {
                    assert(Solution::sub_or(nums@, l as int, r as int) < k);
                }
                let old_r = r;
                let x = nums[r];
                assert(x == nums@[old_r as int]);
                assert(0 <= nums@[old_r as int] < 1073741824i32);
                let mut b: usize = 0;
                while b < 30
                    invariant
                        b <= 30,
                        cnt.len() == 30,
                        n <= 200000,
                        l <= old_r < n,
                        x == nums@[old_r as int],
                        0 <= x < 1073741824i32,
                        forall |bb: int| 0 <= bb < b ==> cnt[bb] as int == count_bit(nums@, l as int, old_r as int + 1, bb as u32),
                        forall |bb: int| b <= bb < 30 ==> cnt[bb] as int == count_bit(nums@, l as int, old_r as int, bb as u32),
                        forall |bb: int| 0 <= bb < 30 ==> 0 <= #[trigger] cnt[bb] as int <= n as int,
                    decreases 30 - b,
                {
                    let bit_here = bit_set_exec(x, b as u32);
                    assert(count_bit(nums@, l as int, old_r as int + 1, b as u32)
                        == count_bit(nums@, l as int, old_r as int, b as u32)
                            + (if bit_set(nums@[old_r as int], b as u32) { 1int } else { 0int }));
                    proof {
                        lemma_count_bit_bound(nums@, l as int, old_r as int + 1, b as u32);
                    }
                    assert(0 <= cnt[b as int] as int <= n as int);
                    if bit_here {
                        assert(cnt[b as int] as int + 1 <= n as int);
                        cnt.set(b, cnt[b] + 1);
                    }
                    b += 1;
                }
                window_or = window_or | x;
                assert(Solution::sub_or(nums@, l as int, old_r as int + 1)
                    == (Solution::sub_or(nums@, l as int, old_r as int) | nums@[old_r as int]));
                r += 1;
                assert forall |e: int| l < e < r as int implies Solution::sub_or(nums@, l as int, e) < k by {
                }
            }
            assert(r > l);
            let old_best = best;
            assert(old_best as int == Solution::min_len_prefix(nums@, k, l as int));

            if window_or >= k {
                proof { lemma_start_upto_first_hit(nums@, k, l as int, r as int, n as int); }
                assert(Solution::min_len_start_upto(nums@, k, l as int, n as int) == r as int - l as int);
                assert(n <= 200000);
                assert(r - l <= n);
                assert(0 <= (r - l) as int <= 200000int);
                let candidate: i32 = (r - l) as i32;
                assert(candidate as int == r as int - l as int);
                if candidate < best {
                    best = candidate;
                } else {
                    best = old_best;
                }
            } else {
                proof {
                    lemma_start_upto_all_invalid(nums@, k, l as int, n as int);
                    lemma_min_len_prefix_bound(nums@, k, l as int);
                }
                assert(Solution::min_len_start_upto(nums@, k, l as int, n as int) == n as int + 1);
                assert(old_best as int <= n as int + 1);
                best = old_best;
            }
            assert(best as int == Solution::imin(
                Solution::min_len_prefix(nums@, k, l as int),
                Solution::min_len_start_upto(nums@, k, l as int, n as int)));
            assert(best as int == Solution::min_len_prefix(nums@, k, l as int + 1));

            let removed = nums[l];
            let old_l = l;
            assert(removed == nums@[old_l as int]);
            assert(0 <= nums@[old_l as int] < 1073741824i32);
            let mut b2: usize = 0;
            while b2 < 30
                invariant
                    b2 <= 30,
                    cnt.len() == 30,
                    n == nums.len(),
                    n <= 200000,
                    old_l < r <= n,
                    removed == nums@[old_l as int],
                    0 <= removed < 1073741824i32,
                    forall |bb: int| 0 <= bb < b2 ==> cnt[bb] as int == count_bit(nums@, old_l as int + 1, r as int, bb as u32),
                    forall |bb: int| b2 <= bb < 30 ==> cnt[bb] as int == count_bit(nums@, old_l as int, r as int, bb as u32),
                    forall |bb: int| 0 <= bb < 30 ==> 0 <= #[trigger] cnt[bb] as int <= n as int,
                decreases 30 - b2,
            {
                let bit_here = bit_set_exec(removed, b2 as u32);
                proof {
                    lemma_count_bit_start_step(nums@, old_l as int, r as int, b2 as u32);
                    lemma_count_bit_bound(nums@, old_l as int + 1, r as int, b2 as u32);
                }
                if bit_here {
                    cnt.set(b2, cnt[b2] - 1);
                }
                b2 += 1;
            }

            let mut new_or: i32 = 0;
            let mut b3: usize = 0;
            while b3 < 30
                invariant
                    b3 <= 30,
                    cnt.len() == 30,
                    old_l + 1 <= r <= n,
                    forall |bb: int| 0 <= bb < 30 ==> cnt[bb] as int == count_bit(nums@, old_l as int + 1, r as int, bb as u32),
                    new_or == cnt_bits_value(cnt@.map_values(|x: i32| x as int), b3 as int),
                decreases 30 - b3,
            {
                if cnt[b3] > 0 {
                    new_or = new_or | (1i32 << (b3 as u32));
                }
                b3 += 1;
            }
            proof {
                lemma_cnt_bits_value_matches_sub_or(nums@, old_l as int + 1, r as int, cnt@.map_values(|x: i32| x as int));
            }
            window_or = new_or;
            l += 1;

            assert forall |e: int| l < e < r as int implies Solution::sub_or(nums@, l as int, e) < k by {
                lemma_sub_or_mono_left(nums@, l as int - 1, l as int, e);
            }
        }

        if best <= n as i32 {
            best
        } else {
            -1
        }
    }
}

}
