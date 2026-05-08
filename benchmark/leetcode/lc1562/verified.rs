use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn bits_at_step(arr: Seq<i32>, n: int, step: int) -> Seq<bool>
        decreases step when step >= 0
    {
        if step <= 0 {
            Seq::new((n + 2) as nat, |i: int| false)
        } else {
            Self::bits_at_step(arr, n, step - 1).update(arr[step - 1] as int, true)
        }
    }

    pub open spec fn is_group_start(bits: Seq<bool>, n: int, m: int, l: int) -> bool {
        1 <= l && l + m - 1 <= n
        && (forall |p: int| l <= p < l + m ==> bits[p])
        && !bits[l - 1]
        && !bits[l + m]
    }

    pub open spec fn has_group_in_bits(bits: Seq<bool>, n: int, m: int) -> bool {
        exists |l: int| #[trigger] Self::is_group_start(bits, n, m, l)
    }

    pub open spec fn has_group_of_size(arr: Seq<i32>, n: int, step: int, m: int) -> bool {
        Self::has_group_in_bits(Self::bits_at_step(arr, n, step), n, m)
    }

    pub open spec fn no_group_after(arr: Seq<i32>, n: int, m: int, from: int) -> bool {
        forall |step: int| from < step && step <= n ==>
            !Self::has_group_of_size(arr, n, step, m)
    }

    pub open spec fn no_group_between(arr: Seq<i32>, n: int, m: int, from: int, to: int) -> bool {
        forall |step: int| from < step && step <= to ==>
            !Self::has_group_of_size(arr, n, step, m)
    }

    pub open spec fn group_len_right(bits: Seq<bool>, pos: int) -> int
        decreases bits.len() - pos when 0 <= pos
    {
        if pos < 0 || pos >= bits.len() as int || !bits[pos] { 0 }
        else { 1 + Self::group_len_right(bits, pos + 1) }
    }

    pub open spec fn group_len_left(bits: Seq<bool>, pos: int) -> int
        decreases pos + 1 when pos >= -1
    {
        if pos < 0 || pos >= bits.len() as int || !bits[pos] { 0 }
        else { 1 + Self::group_len_left(bits, pos - 1) }
    }

    pub open spec fn num_groups_of_size(bits: Seq<bool>, n: int, m: int, pos: int) -> int
        decreases n + 1 - pos when pos >= 1
    {
        if pos > n { 0 }
        else {
            let is_start = bits[pos] && !bits[pos - 1];
            let is_m_group = is_start && Self::group_len_right(bits, pos) == m;
            (if is_m_group { 1int } else { 0int }) + Self::num_groups_of_size(bits, n, m, pos + 1)
        }
    }

    proof fn lemma_bits_at_step_len(arr: Seq<i32>, n: int, step: int)
        requires
            n >= 0,
            step >= 0,
            arr.len() >= step,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] && arr[i] <= n,
        ensures
            Self::bits_at_step(arr, n, step).len() == n + 2,
        decreases step,
    {
        if step > 0 {
            Self::lemma_bits_at_step_len(arr, n, step - 1);
        }
    }

    proof fn lemma_bits_at_step_sentinels(arr: Seq<i32>, n: int, step: int)
        requires
            n >= 0,
            step >= 0,
            arr.len() >= step,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] && arr[i] <= n,
        ensures
            Self::bits_at_step(arr, n, step).len() == n + 2,
            !Self::bits_at_step(arr, n, step)[0],
            !Self::bits_at_step(arr, n, step)[n + 1],
        decreases step,
    {
        if step <= 0 {
        } else {
            Self::lemma_bits_at_step_sentinels(arr, n, step - 1);
            let prev = Self::bits_at_step(arr, n, step - 1);
            let a = arr[step - 1] as int;
            assert(1 <= a <= n);
            assert(Self::bits_at_step(arr, n, step) == prev.update(a, true));
        }
    }

    proof fn lemma_bits_at_step_monotone(arr: Seq<i32>, n: int, step: int, pos: int)
        requires
            n >= 0,
            step >= 1,
            arr.len() >= step,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] && arr[i] <= n,
            0 <= pos < n + 2,
            Self::bits_at_step(arr, n, step - 1)[pos],
        ensures
            Self::bits_at_step(arr, n, step)[pos],
        decreases step,
    {
        Self::lemma_bits_at_step_len(arr, n, step - 1);
    }

    proof fn lemma_bits_step_update(arr: Seq<i32>, n: int, step: int, pos: int)
        requires
            n >= 0,
            step >= 1,
            arr.len() >= step,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] && arr[i] <= n,
            0 <= pos < n + 2,
        ensures
            Self::bits_at_step(arr, n, step).len() == n + 2,
            Self::bits_at_step(arr, n, step)[pos] == (
                arr[step - 1] as int == pos || Self::bits_at_step(arr, n, step - 1)[pos]
            ),
        decreases step,
    {
        Self::lemma_bits_at_step_len(arr, n, step - 1);
    }

    proof fn lemma_glr_nonneg(bits: Seq<bool>, pos: int)
        requires 0 <= pos,
        ensures Self::group_len_right(bits, pos) >= 0,
        decreases bits.len() - pos,
    {
        if pos < bits.len() as int && bits[pos] {
            Self::lemma_glr_nonneg(bits, pos + 1);
        }
    }

    proof fn lemma_gll_nonneg(bits: Seq<bool>, pos: int)
        requires pos >= -1,
        ensures Self::group_len_left(bits, pos) >= 0,
        decreases pos + 1,
    {
        if pos >= 0 && pos < bits.len() as int && bits[pos] {
            Self::lemma_gll_nonneg(bits, pos - 1);
        }
    }

    proof fn lemma_glr_same_prefix(bits1: Seq<bool>, bits2: Seq<bool>, pos: int, barrier: int)
        requires
            bits1.len() == bits2.len(),
            0 <= pos <= barrier,
            barrier < bits1.len(),
            forall |p: int| pos <= p <= barrier ==> bits1[p] == bits2[p],
            !bits1[barrier],
        ensures
            Self::group_len_right(bits1, pos) == Self::group_len_right(bits2, pos),
        decreases barrier - pos + 1,
    {
        if !bits1[pos] {
        } else {
            Self::lemma_glr_same_prefix(bits1, bits2, pos + 1, barrier);
        }
    }

    proof fn lemma_glr_same_suffix(bits1: Seq<bool>, bits2: Seq<bool>, pos: int)
        requires
            bits1.len() == bits2.len(),
            0 <= pos,
            forall |p: int| pos <= p < bits1.len() ==> bits1[p] == bits2[p],
        ensures
            Self::group_len_right(bits1, pos) == Self::group_len_right(bits2, pos),
        decreases bits1.len() - pos,
    {
        if pos >= bits1.len() as int || !bits1[pos] {
        } else {
            Self::lemma_glr_same_suffix(bits1, bits2, pos + 1);
        }
    }

    proof fn lemma_glr_consecutive(bits: Seq<bool>, start: int, end: int)
        requires
            0 <= start <= end,
            end < bits.len(),
            forall |p: int| start <= p <= end ==> bits[p],
            end + 1 >= bits.len() as int || !bits[end + 1],
        ensures
            Self::group_len_right(bits, start) == end - start + 1,
        decreases end - start + 1,
    {
        if start == end {
            assert(bits[start]);
            Self::lemma_glr_nonneg(bits, start + 1);
            if start + 1 < bits.len() as int {
                assert(!bits[start + 1]);
            }
        } else {
            Self::lemma_glr_consecutive(bits, start + 1, end);
        }
    }

    proof fn lemma_gll_consecutive(bits: Seq<bool>, start: int, end: int)
        requires
            0 <= start <= end,
            end < bits.len(),
            forall |p: int| start <= p <= end ==> bits[p],
            start == 0 || !bits[start - 1],
        ensures
            Self::group_len_left(bits, end) == end - start + 1,
        decreases end - start + 1,
    {
        if start == end {
            assert(bits[end]);
            Self::lemma_gll_nonneg(bits, end - 1);
            if start > 0 {
                assert(!bits[start - 1]);
            }
        } else {
            Self::lemma_gll_consecutive(bits, start, end - 1);
        }
    }

    proof fn lemma_ngs_nonneg(bits: Seq<bool>, n: int, m: int, pos: int)
        requires
            bits.len() == n + 2,
            m >= 1,
            pos >= 1,
        ensures
            Self::num_groups_of_size(bits, n, m, pos) >= 0,
        decreases n + 1 - pos,
    {
        if pos > n {
        } else {
            Self::lemma_ngs_nonneg(bits, n, m, pos + 1);
        }
    }

    proof fn lemma_ngs_bound(bits: Seq<bool>, n: int, m: int, pos: int)
        requires
            bits.len() == n + 2,
            m >= 1,
            1 <= pos <= n + 1,
        ensures
            Self::num_groups_of_size(bits, n, m, pos) <= n - pos + 1,
        decreases n + 1 - pos,
    {
        if pos > n {
        } else {
            Self::lemma_ngs_bound(bits, n, m, pos + 1);
        }
    }

    proof fn lemma_ngs_monotone(bits: Seq<bool>, n: int, m: int, pos1: int, pos2: int)
        requires
            bits.len() == n + 2,
            m >= 1,
            1 <= pos1 <= pos2,
        ensures
            Self::num_groups_of_size(bits, n, m, pos1) >= Self::num_groups_of_size(bits, n, m, pos2),
        decreases pos2 - pos1,
    {
        if pos1 == pos2 {
        } else {
            Self::lemma_ngs_monotone(bits, n, m, pos1 + 1, pos2);
            Self::lemma_ngs_nonneg(bits, n, m, pos1 + 1);
        }
    }

    proof fn lemma_ngs_positive_witness(bits: Seq<bool>, n: int, m: int, l: int)
        requires
            bits.len() == n + 2,
            m >= 1,
            1 <= l,
            l + m - 1 <= n,
            forall |p: int| l <= p < l + m ==> bits[p],
            !bits[l - 1],
            !bits[l + m],
        ensures
            Self::num_groups_of_size(bits, n, m, 1) >= 1,
    {
        Self::lemma_glr_consecutive(bits, l, l + m - 1);
        Self::lemma_ngs_nonneg(bits, n, m, l + 1);
        Self::lemma_ngs_monotone(bits, n, m, 1, l);
    }

    proof fn lemma_ngs_zero_means_no_group(bits: Seq<bool>, n: int, m: int, pos: int, l: int)
        requires
            bits.len() == n + 2,
            m >= 1,
            1 <= pos,
            Self::num_groups_of_size(bits, n, m, pos) == 0,
            pos <= l,
            l + m - 1 <= n,
            forall |p: int| l <= p < l + m ==> bits[p],
            !bits[l - 1],
        ensures
            bits[l + m],
        decreases n + 1 - pos,
    {
        if pos > n {
            assert(l > n);
        } else {
            Self::lemma_ngs_nonneg(bits, n, m, pos + 1);
            if pos == l {
                
                
                if !bits[l + m] {
                    Self::lemma_glr_consecutive(bits, l, l + m - 1);
                    
                    
                    
                }
            } else {
                Self::lemma_ngs_zero_means_no_group(bits, n, m, pos + 1, l);
            }
        }
    }

    proof fn lemma_ngs_update(
        old_bits: Seq<bool>, new_bits: Seq<bool>,
        n: int, m: int, a: int, left: int, right: int, pos: int,
    )
        requires
            old_bits.len() == n + 2,
            new_bits.len() == n + 2,
            n >= 1,
            m >= 1,
            1 <= a <= n,
            !old_bits[a],
            !old_bits[0],
            !old_bits[n + 1],
            new_bits == old_bits.update(a, true),
            left >= 0,
            right >= 0,
            left == Self::group_len_left(old_bits, a - 1),
            right == Self::group_len_right(old_bits, a + 1),
            forall |p: int| a - left <= p < a ==> old_bits[p],
            a - left >= 1,
            a + right <= n,
            left > 0 ==> !old_bits[a - left - 1],
            right > 0 ==> !old_bits[a + right + 1],
            1 <= pos <= n + 1,
        ensures
            Self::num_groups_of_size(new_bits, n, m, pos) ==
                Self::num_groups_of_size(old_bits, n, m, pos)
                + (if pos <= a - left && left + right + 1 == m { 1int } else { 0 })
                - (if pos <= a - left && left > 0 && left == m { 1int } else { 0 })
                - (if pos <= a + 1 && right > 0 && right == m { 1int } else { 0 }),
        decreases n + 1 - pos,
    {
        if pos > n {
            return;
        }

        
        if right > 0 {
            if !old_bits[a + 1] {
                Self::lemma_glr_nonneg(old_bits, a + 2);
                assert(false);
            }
            Self::lemma_glr_to_bits(old_bits, a + 1, right);
        }

        Self::lemma_ngs_update(old_bits, new_bits, n, m, a, left, right, pos + 1);

        let old_is_start = old_bits[pos] && !old_bits[pos - 1];
        let new_is_start = new_bits[pos] && !new_bits[pos - 1];

        if pos < a - left {
            assert(new_bits[pos] == old_bits[pos]);
            assert(new_bits[pos - 1] == old_bits[pos - 1]);
            if old_is_start {
                if left > 0 {
                    assert(!old_bits[a - left - 1]);
                    Self::lemma_glr_same_prefix(old_bits, new_bits, pos, a - left - 1);
                } else {
                    
                    
                    if old_bits[a - 1] {
                        Self::lemma_gll_nonneg(old_bits, a - 2);
                        assert(false);
                    }
                    Self::lemma_glr_same_prefix(old_bits, new_bits, pos, a - 1);
                }
            }
        } else if pos == a - left {
            if left > 0 {
                assert(old_bits[pos]);
                assert(!old_bits[pos - 1]);
                assert(old_is_start);
                Self::lemma_glr_consecutive(old_bits, a - left, a - 1);
                assert(Self::group_len_right(old_bits, pos) == left);

                assert(new_bits[pos] == old_bits[pos]);
                assert(new_bits[pos - 1] == old_bits[pos - 1]);
                assert(new_is_start);
                
                if right > 0 {
                    assert(!old_bits[a + right + 1]);
                    assert(a + right + 1 != a);
                    assert(!new_bits[a + right + 1]);
                } else {
                    
                    if old_bits[a + 1] {
                        Self::lemma_glr_nonneg(old_bits, a + 2);
                        assert(false);
                    }
                    assert(!new_bits[a + 1]);
                }
                Self::lemma_glr_consecutive(new_bits, a - left, a + right);
                assert(Self::group_len_right(new_bits, pos) == left + right + 1);
            } else {
                assert(pos == a);
                assert(!old_bits[a]);
                assert(!old_is_start);

                
                if old_bits[a - 1] {
                    Self::lemma_gll_nonneg(old_bits, a - 2);
                    assert(false);
                }
                assert(new_bits[a]);
                assert(!new_bits[a - 1]);
                assert(new_is_start);
                
                if right > 0 {
                    assert(!old_bits[a + right + 1]);
                    assert(a + right + 1 != a);
                    assert(!new_bits[a + right + 1]);
                } else {
                    if old_bits[a + 1] {
                        Self::lemma_glr_nonneg(old_bits, a + 2);
                        assert(false);
                    }
                    assert(!new_bits[a + 1]);
                }
                Self::lemma_glr_consecutive(new_bits, a, a + right);
                assert(Self::group_len_right(new_bits, pos) == right + 1);
            }
        } else if pos > a - left && pos <= a {
            if left > 0 {
                assert(a - left <= pos - 1 && pos - 1 < a);
                assert(old_bits[pos - 1]);
                assert(new_bits[pos - 1] == old_bits[pos - 1]);
                assert(!old_is_start);
                assert(!new_is_start);
            } else {
                assert(pos == a + 1 || pos == a);
                if pos == a {
                } else {
                }
            }
        } else if pos == a + 1 {
            if right > 0 {
                assert(old_bits[a + 1]);
                assert(!old_bits[a]);
                assert(old_is_start);
                Self::lemma_glr_consecutive(old_bits, a + 1, a + right);
                assert(Self::group_len_right(old_bits, pos) == right);

                assert(new_bits[a]);
                assert(!new_is_start);
            } else {
                
                
                if old_bits[a + 1] {
                    Self::lemma_glr_nonneg(old_bits, a + 2);
                    assert(false);
                }
                assert(!old_bits[a + 1]);
                assert(!old_is_start);
                assert(!new_is_start || new_bits[a]);
            }
        } else if pos > a + 1 && pos <= a + right {
            
            assert(a + 1 <= pos - 1 && pos - 1 < a + 1 + right);
            assert(old_bits[pos - 1]);
            assert(new_bits[pos - 1] == old_bits[pos - 1]);
            assert(!old_is_start);
            assert(!new_is_start);
        } else {
            assert(new_bits[pos] == old_bits[pos]);
            assert(new_bits[pos - 1] == old_bits[pos - 1]);
            if old_is_start {
                Self::lemma_glr_same_suffix(old_bits, new_bits, pos);
            }
        }
    }

    proof fn lemma_gll_to_bits(bits: Seq<bool>, pos: int, len: int)
        requires
            bits.len() > pos,
            pos >= 0,
            len >= 1,
            Self::group_len_left(bits, pos) == len,
            bits[pos],
        ensures
            forall |p: int| pos - len + 1 <= p <= pos ==> bits[p],
            pos - len >= -1,
            pos - len + 1 >= 0,
            (pos - len >= 0) ==> !bits[pos - len],
        decreases pos + 1,
    {
        if len == 1 {
            Self::lemma_gll_nonneg(bits, pos - 1);
            
            
            if pos - 1 >= 0 && bits[pos - 1] {
                Self::lemma_gll_nonneg(bits, pos - 2);
                assert(false);
            }
        } else {
            assert(bits[pos]);
            assert(Self::group_len_left(bits, pos) == 1 + Self::group_len_left(bits, pos - 1));
            Self::lemma_gll_nonneg(bits, pos - 1);
            assert(Self::group_len_left(bits, pos - 1) == len - 1);
            assert(bits[pos - 1]);
            Self::lemma_gll_to_bits(bits, pos - 1, len - 1);
        }
    }

    proof fn lemma_glr_to_bits(bits: Seq<bool>, pos: int, len: int)
        requires
            bits.len() > pos,
            pos >= 0,
            len >= 1,
            Self::group_len_right(bits, pos) == len,
            bits[pos],
        ensures
            forall |p: int| pos <= p < pos + len ==> bits[p],
            pos + len <= bits.len(),
            (pos + len < bits.len()) ==> !bits[pos + len],
        decreases bits.len() - pos,
    {
        if len == 1 {
            Self::lemma_glr_nonneg(bits, pos + 1);
            
            
            if pos + 1 < bits.len() as int && bits[pos + 1] {
                Self::lemma_glr_nonneg(bits, pos + 2);
                assert(false);
            }
        } else {
            assert(bits[pos]);
            assert(Self::group_len_right(bits, pos) == 1 + Self::group_len_right(bits, pos + 1));
            Self::lemma_glr_nonneg(bits, pos + 1);
            assert(Self::group_len_right(bits, pos + 1) == len - 1);
            assert(bits[pos + 1]);
            Self::lemma_glr_to_bits(bits, pos + 1, len - 1);
        }
    }

    proof fn lemma_not_set_before(arr: Seq<i32>, n: int, step: int, pos: int)
        requires
            n >= 1,
            step >= 0,
            arr.len() >= step,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] && arr[i] <= n,
            forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j],
            1 <= pos <= n,
            exists |j: int| 0 <= j < step && arr[j] as int == pos,
        ensures
            Self::bits_at_step(arr, n, step)[pos],
        decreases step,
    {
        Self::lemma_bits_at_step_len(arr, n, step);
        if step <= 0 {
        } else {
            Self::lemma_bits_at_step_len(arr, n, step - 1);
            let a = arr[step - 1] as int;
            if a == pos {
            } else {
                let j = choose |j: int| 0 <= j < step && arr[j] as int == pos;
                assert(j < step - 1);
                Self::lemma_not_set_before(arr, n, step - 1, pos);
            }
        }
    }

    proof fn lemma_not_set_after(arr: Seq<i32>, n: int, step: int, pos: int)
        requires
            n >= 1,
            step >= 0,
            arr.len() >= step,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] && arr[i] <= n,
            forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j],
            1 <= pos <= n,
            !Self::bits_at_step(arr, n, step)[pos],
        ensures
            forall |j: int| 0 <= j < step ==> arr[j] as int != pos,
        decreases step,
    {
        Self::lemma_bits_at_step_len(arr, n, step);
        if step <= 0 {
        } else {
            Self::lemma_bits_at_step_len(arr, n, step - 1);
            let a = arr[step - 1] as int;
            assert(Self::bits_at_step(arr, n, step) == Self::bits_at_step(arr, n, step - 1).update(a, true));
            assert(a != pos);
            assert(!Self::bits_at_step(arr, n, step - 1)[pos]);
            Self::lemma_not_set_after(arr, n, step - 1, pos);
        }
    }

    proof fn lemma_unset_before_step(arr: Seq<i32>, n: int, step: int, pos: int)
        requires
            n >= 1,
            step >= 0,
            arr.len() >= step,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] && arr[i] <= n,
            1 <= pos <= n,
            forall |j: int| 0 <= j < step ==> arr[j] as int != pos,
        ensures
            !Self::bits_at_step(arr, n, step)[pos],
        decreases step,
    {
        Self::lemma_bits_at_step_len(arr, n, step);
        if step <= 0 {
        } else {
            Self::lemma_bits_at_step_len(arr, n, step - 1);
            assert(arr[step - 1] as int != pos);
            Self::lemma_unset_before_step(arr, n, step - 1, pos);
        }
    }

    proof fn lemma_all_false_ngs(bits: Seq<bool>, n: int, m: int, pos: int)
        requires
            bits.len() == n + 2,
            m >= 1,
            pos >= 1,
            forall |p: int| 0 <= p < bits.len() ==> !bits[p],
        ensures
            Self::num_groups_of_size(bits, n, m, pos) == 0,
        decreases n + 1 - pos,
    {
        if pos > n {
        } else {
            Self::lemma_all_false_ngs(bits, n, m, pos + 1);
        }
    }

    pub fn find_latest_step(arr: Vec<i32>, m: i32) -> (res: i32)
        requires
            arr.len() >= 1,
            arr.len() <= 100_000,
            1 <= m <= arr.len() as i32,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= arr.len() as i32,
            forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j],
        ensures
            res == -1 || (1 <= res && res <= arr.len() as i32),
            res == -1 ==> Self::no_group_after(arr@, arr@.len() as int, m as int, 0),
            res >= 1 ==> Self::has_group_of_size(arr@, arr@.len() as int, res as int, m as int),
            res >= 1 ==> Self::no_group_after(arr@, arr@.len() as int, m as int, res as int),
    {
        let n = arr.len();

        let mut length: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        assert(n <= 100_000usize);
        while idx < n + 2
            invariant
                length.len() == idx,
                idx <= n + 2,
                n == arr.len(),
                n <= 100_000,
                forall |j: int| 0 <= j < idx as int ==> length@[j] == 0i32,
            decreases n + 2 - idx,
        {
            length.push(0);
            idx = idx + 1;
        }

        let mut count_m: i32 = 0;
        let mut res: i32 = -1;
        let ghost mut bits: Seq<bool> = Seq::new((n + 2) as nat, |i: int| false);

        proof {
            assert(bits =~= Self::bits_at_step(arr@, n as int, 0));

            
            Self::lemma_all_false_ngs(bits, n as int, m as int, 1);

            
            assert(!Self::has_group_in_bits(bits, n as int, m as int)) by {
                if Self::has_group_in_bits(bits, n as int, m as int) {
                    let l = choose |l: int|
                        #[trigger] Self::is_group_start(bits, n as int, m as int, l);
                    assert(bits[l]); 
                }
            };
        }

        let mut i: usize = 0;
        while i < n
            invariant
                n == arr.len(),
                n >= 1,
                n <= 100_000,
                0 <= i <= n,
                1 <= m <= n as i32,
                forall |k: int| 0 <= k < n ==> 1 <= #[trigger] arr@[k] <= n as i32,
                forall |k: int, l: int| 0 <= k < l < n ==> arr@[k] != arr@[l],

                length.len() == n + 2,
                bits.len() == n + 2,
                bits =~= Self::bits_at_step(arr@, n as int, i as int),
                !bits[0],
                !bits[n + 1 as int],

                forall |p: int| 1 <= p <= n as int && !bits[p] ==> length@[p] == 0,
                length@[0] == 0i32,
                length@[(n + 1) as int] == 0i32,
                forall |p: int| 1 <= p <= n as int && bits[p] && !bits[p - 1] ==>
                    length@[p] as int == Self::group_len_right(bits, p),
                forall |p: int| 1 <= p <= n as int && bits[p] && !bits[p + 1] ==>
                    length@[p] as int == Self::group_len_left(bits, p),

                forall |p: int| 0 <= p < (n + 2) as int ==> 0 <= #[trigger] length@[p] && length@[p] <= n as i32,

                count_m as int == Self::num_groups_of_size(bits, n as int, m as int, 1),
                count_m >= 0,
                count_m <= n as i32,

                res == -1 || (1 <= res <= i as i32),
                (res == -1) ==> !Self::has_group_in_bits(bits, n as int, m as int),
                (res == -1) ==> Self::no_group_between(arr@, n as int, m as int, 0, i as int),
                (res >= 1) ==> Self::has_group_of_size(arr@, n as int, res as int, m as int),
                (res >= 1) ==> Self::no_group_between(arr@, n as int, m as int, res as int, i as int),

                Self::has_group_in_bits(bits, n as int, m as int) <==>
                    Self::num_groups_of_size(bits, n as int, m as int, 1) > 0,
            decreases n - i,
        {
            let a = arr[i] as usize;

            proof {
                assert(1 <= a <= n);
                
                assert forall |j: int| 0 <= j < i as int implies arr@[j] as int != a as int by {
                    assert(arr@[j] != arr@[i as int]); 
                };
                Self::lemma_unset_before_step(arr@, n as int, i as int, a as int);
                assert(!bits[a as int]);
            }

            let left = length[a - 1];
            let right = length[a + 1];

            proof {
                Self::lemma_glr_nonneg(bits, (a + 1) as int);
                Self::lemma_gll_nonneg(bits, (a - 1) as int);

                if bits[(a - 1) as int] {
                    assert(!bits[a as int]);
                    assert(length@[(a - 1) as int] as int == Self::group_len_left(bits, (a - 1) as int));
                } else {
                    assert(Self::group_len_left(bits, (a - 1) as int) == 0);
                }

                if bits[(a + 1) as int] {
                    assert(!bits[a as int]);
                    assert(length@[(a + 1) as int] as int == Self::group_len_right(bits, (a + 1) as int));
                } else {
                    assert(Self::group_len_right(bits, (a + 1) as int) == 0);
                }
            }

            let new_len = left + right + 1;
            let ghost old_bits = bits;
            let ghost left_int = left as int;
            let ghost right_int = right as int;
            let ghost a_int = a as int;

            proof {
                
                
                if left_int > 0 {
                    
                    assert(length@[0] == 0i32);
                    assert((a - 1) as int != 0);
                    assert(1 <= (a - 1) as int && (a - 1) as int <= n as int);
                    
                    assert(bits[(a - 1) as int]);
                    assert(!bits[a as int]);
                }
                if right_int > 0 {
                    
                    assert(length@[(n + 1) as int] == 0i32);
                    assert((a + 1) as int != (n + 1) as int);
                    assert(1 <= (a + 1) as int && (a + 1) as int <= n as int);
                    assert(bits[(a + 1) as int]);
                    assert(!bits[a as int]);
                }

                bits = bits.update(a as int, true);

                assert(bits =~= Self::bits_at_step(arr@, n as int, (i + 1) as int)) by {
                    Self::lemma_bits_at_step_len(arr@, n as int, i as int);
                };

                Self::lemma_bits_at_step_sentinels(arr@, n as int, (i + 1) as int);

                if left_int > 0 {
                    Self::lemma_gll_to_bits(old_bits, (a - 1) as int, left_int);
                }
                if right_int > 0 {
                    Self::lemma_glr_to_bits(old_bits, (a + 1) as int, right_int);
                }
            }

            length.set(a - left as usize, new_len);
            length.set(a + right as usize, new_len);

            if left == m {
                count_m = count_m - 1;
            }
            if right == m {
                count_m = count_m - 1;
            }
            if new_len == m {
                count_m = count_m + 1;
            }

            proof {
                Self::lemma_ngs_update(
                    old_bits, bits, n as int, m as int, a_int, left_int, right_int, 1,
                );

                assert(count_m as int == Self::num_groups_of_size(bits, n as int, m as int, 1));

                Self::lemma_ngs_nonneg(bits, n as int, m as int, 1);
                Self::lemma_ngs_bound(bits, n as int, m as int, 1);

                
                assert(a_int + right_int + 1 >= bits.len() as int
                    || !bits[(a_int + right_int + 1) as int]) by {
                    assert(a_int + right_int + 1 != a_int);
                    if a_int + right_int + 1 < bits.len() as int {
                        if right_int > 0 {
                            
                        } else {
                            
                            if old_bits[(a_int + 1) as int] {
                                Self::lemma_glr_nonneg(old_bits, a_int + 2);
                                assert(Self::group_len_right(old_bits, a_int + 1) >= 1);
                                assert(false);
                            }
                        }
                    }
                };

                assert forall |p: int| 1 <= p <= n as int && !bits[p]
                    implies length@[p] == 0
                by {
                    if p == a_int - left_int {
                        if left_int > 0 {
                            assert(old_bits[p]);
                            assert(bits[p]);
                        } else {
                            assert(p == a_int);
                            assert(bits[a_int]);
                        }
                    } else if p == a_int + right_int {
                        if right_int > 0 {
                            assert(old_bits[p]);
                            assert(bits[p]);
                        } else {
                            assert(p == a_int);
                            assert(bits[a_int]);
                        }
                    } else {
                        assert(p != a_int - left_int && p != a_int + right_int);
                        assert(!bits[p]);
                    }
                };

                assert forall |p: int| 1 <= p <= n as int && bits[p] && !bits[p - 1]
                    implies length@[p] as int == Self::group_len_right(bits, p)
                by {
                    if p == a_int - left_int {
                        Self::lemma_glr_consecutive(bits, a_int - left_int, a_int + right_int);
                        assert(Self::group_len_right(bits, p) == left_int + right_int + 1);
                        assert(length@[p] == new_len);
                    } else if p == a_int && left_int > 0 {
                        assert(bits[p - 1]);
                    } else if p == a_int + 1 && right_int > 0 {
                        assert(bits[a_int]);
                        assert(bits[p - 1]);
                    } else if p != a_int - left_int && p != a_int + right_int {
                        assert(length@[p] == length@.update(
                            (a_int - left_int) as int, new_len).update(
                            (a_int + right_int) as int, new_len)[p]
                            || p == a_int - left_int || p == a_int + right_int);
                        if old_bits[p] && !old_bits[p - 1] {
                            if p < a_int - left_int {
                                if left_int > 0 {
                                    Self::lemma_glr_same_prefix(
                                        old_bits, bits, p, a_int - left_int - 1);
                                } else {
                                    
                                    if old_bits[a_int - 1] {
                                        Self::lemma_gll_nonneg(old_bits, a_int - 2);
                                        assert(false);
                                    }
                                    Self::lemma_glr_same_prefix(old_bits, bits, p, a_int - 1);
                                }
                            } else {
                                Self::lemma_glr_same_suffix(old_bits, bits, p);
                            }
                        } else {
                            if !old_bits[p] {
                                assert(p == a_int);
                                if left_int == 0 {
                                    assert(p == a_int - left_int);
                                }
                            }
                        }
                    } else {
                        if p == a_int + right_int && p != a_int - left_int {
                            if right_int > 0 {
                                assert(bits[p - 1]);
                            } else {
                                assert(p == a_int);
                                assert(p == a_int - left_int);
                            }
                        }
                    }
                };

                assert forall |p: int| 1 <= p <= n as int && bits[p] && !bits[p + 1]
                    implies length@[p] as int == Self::group_len_left(bits, p)
                by {
                    if p == a_int + right_int {
                        
                        if left_int > 0 {
                            assert(!old_bits[a_int - left_int - 1]);
                            assert(a_int - left_int - 1 != a_int);
                            assert(!bits[a_int - left_int - 1]);
                        } else {
                            
                            
                            if old_bits[a_int - 1] {
                                Self::lemma_gll_nonneg(old_bits, a_int - 2);
                                assert(false);
                            }
                            assert(!bits[a_int - 1]);
                        }
                        Self::lemma_gll_consecutive(bits, a_int - left_int, a_int + right_int);
                        assert(Self::group_len_left(bits, p) == left_int + right_int + 1);
                        assert(length@[p] == new_len);
                    } else if p == a_int && right_int > 0 {
                        assert(bits[p + 1]);
                    } else if p == a_int - 1 && left_int > 0 {
                        assert(bits[a_int]);
                        assert(bits[p + 1]);
                    } else if p != a_int - left_int && p != a_int + right_int {
                        if old_bits[p] && !old_bits[p + 1] {
                            if p > a_int + right_int {
                                Self::lemma_gll_nonneg(old_bits, p - 1);
                                let ghost gl = Self::group_len_left(old_bits, p);
                                assert(gl >= 1) by {
                                    Self::lemma_gll_nonneg(old_bits, p - 1);
                                };
                                Self::lemma_gll_to_bits(old_bits, p, gl);
                                
                                if p - gl == a_int {
                                    
                                    assert(old_bits[a_int + 1]);
                                    if right_int > 0 {
                                        assert(!old_bits[a_int + right_int + 1]);
                                        assert(a_int + right_int + 1 <= p);
                                        assert(false);
                                    } else {
                                        Self::lemma_glr_nonneg(old_bits, a_int + 2);
                                        assert(false);
                                    }
                                }
                                Self::lemma_gll_consecutive(bits, p - gl + 1, p);
                            } else if p < a_int - left_int {
                                Self::lemma_gll_nonneg(old_bits, p - 1);
                                let ghost gl = Self::group_len_left(old_bits, p);
                                assert(gl >= 1) by {
                                    Self::lemma_gll_nonneg(old_bits, p - 1);
                                };
                                Self::lemma_gll_to_bits(old_bits, p, gl);
                                
                                Self::lemma_gll_consecutive(bits, p - gl + 1, p);
                            }
                        } else {
                            if !old_bits[p] {
                                assert(p == a_int);
                                if right_int == 0 {
                                    assert(p == a_int + right_int);
                                }
                            }
                        }
                    } else {
                        if p == a_int - left_int && p != a_int + right_int {
                            if left_int > 0 {
                                assert(bits[p + 1]);
                            } else {
                                assert(p == a_int);
                                assert(p == a_int + right_int);
                            }
                        }
                    }
                };

                assert forall |p: int| 0 <= p < (n + 2) as int
                    implies 0 <= #[trigger] length@[p] && length@[p] <= n as i32
                by {
                    if p == (a_int - left_int) as int || p == (a_int + right_int) as int {
                        assert(new_len <= n as i32);
                    }
                };

                
                assert(a_int - left_int >= 1) by {
                    if left_int > 0 {
                        
                        
                        
                    }
                };
                assert(a_int + right_int <= n as int) by {
                    if right_int > 0 {
                        
                        
                    }
                };
                assert(length@[0] == 0i32);
                assert(length@[(n + 1) as int] == 0i32);

                if Self::num_groups_of_size(bits, n as int, m as int, 1) > 0 {
                    assert(Self::has_group_in_bits(bits, n as int, m as int)) by {
                        Self::lemma_ngs_extract_witness(bits, n as int, m as int, 1);
                    };
                } else {
                    assert(!Self::has_group_in_bits(bits, n as int, m as int)) by {
                        if Self::has_group_in_bits(bits, n as int, m as int) {
                            let l = choose |l: int|
                                #[trigger] Self::is_group_start(bits, n as int, m as int, l);
                            Self::lemma_ngs_positive_witness(bits, n as int, m as int, l);
                        }
                    };
                }
            }

            if count_m > 0 {
                proof {
                    assert(Self::has_group_in_bits(bits, n as int, m as int));
                    assert(bits =~= Self::bits_at_step(arr@, n as int, (i + 1) as int));
                }
                res = (i + 1) as i32;
            }

            i = i + 1;
        }

        proof {
            if res == -1 {
                assert(Self::no_group_between(arr@, n as int, m as int, 0, i as int));
                assert(i == n);
                assert(Self::no_group_after(arr@, n as int, m as int, 0));
            } else {
                assert(Self::no_group_between(arr@, n as int, m as int, res as int, i as int));
                assert(i == n);
                assert(Self::no_group_after(arr@, n as int, m as int, res as int));
            }
        }

        res
    }

    proof fn lemma_ngs_extract_witness(bits: Seq<bool>, n: int, m: int, pos: int)
        requires
            bits.len() == n + 2,
            n >= 0,
            m >= 1,
            1 <= pos,
            !bits[n + 1],
            Self::num_groups_of_size(bits, n, m, pos) > 0,
        ensures
            exists |l: int| pos <= l && #[trigger] Self::is_group_start(bits, n, m, l),
        decreases n + 1 - pos,
    {
        if pos > n {
        } else {
            Self::lemma_ngs_nonneg(bits, n, m, pos + 1);
            let is_start = bits[pos] && !bits[pos - 1];
            let is_m_group = is_start && Self::group_len_right(bits, pos) == m;
            if is_m_group {
                Self::lemma_glr_to_bits(bits, pos, m);
                
                
                
                assert(pos + m - 1 <= n);
                assert(pos + m < bits.len() as int);
                assert(!bits[pos + m]);
                assert(!bits[pos - 1]);
                assert(Self::is_group_start(bits, n, m, pos));
            } else {
                Self::lemma_ngs_extract_witness(bits, n, m, pos + 1);
            }
        }
    }
}

}
