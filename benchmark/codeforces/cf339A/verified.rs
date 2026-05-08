use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_digit(seq: Seq<u8>, v: int, end: int) -> nat
    recommends
        0 <= end <= seq.len(),
    decreases end,
{
    if end <= 0 {
        0nat
    } else {
        count_digit(seq, v, end - 1)
            + (if seq[end - 1] as int == v { 1nat } else { 0nat })
    }
}

pub open spec fn sorted(seq: Seq<u8>) -> bool {
    forall|i: int, j: int|
        0 <= i < j < seq.len() ==> #[trigger] seq[i] as int <= #[trigger] seq[j] as int
}

proof fn lemma_three_segment_sorted(seq: Seq<u8>, c1: int, c2: int, c3: int)
    requires
        0 <= c1,
        0 <= c2,
        0 <= c3,
        seq.len() as int == c1 + c2 + c3,
        forall|i: int| 0 <= i < c1 ==> seq[i] as int == 1,
        forall|i: int| c1 <= i < c1 + c2 ==> seq[i] as int == 2,
        forall|i: int| c1 + c2 <= i < c1 + c2 + c3 ==> seq[i] as int == 3,
    ensures
        sorted(seq),
{
    assert(forall|i: int, j: int|
        0 <= i < j < seq.len() ==> seq[i] as int <= seq[j] as int);
}

pub open spec fn input_digits_valid(seq: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < seq.len() ==> 1 <= #[trigger] seq[i] as int <= 3
}

pub open spec fn all_digits_1_2_3(seq: Seq<u8>, end: int) -> bool
    recommends 0 <= end <= seq.len(),
    decreases end,
{
    if end <= 0 {
        true
    } else {
        all_digits_1_2_3(seq, end - 1) && 1 <= seq[end - 1] as int <= 3
    }
}

proof fn lemma_all_digits_at(seq: Seq<u8>, end: int, idx: int)
    requires
        0 <= end <= seq.len(),
        all_digits_1_2_3(seq, end),
        0 <= idx < end,
    ensures
        1 <= seq[idx] as int <= 3,
    decreases end,
{
    if end <= 0 {
    } else if idx == end - 1 {
    } else {
        lemma_all_digits_at(seq, end - 1, idx);
    }
}

proof fn lemma_input_implies_all_upto(seq: Seq<u8>, k: int)
    requires
        input_digits_valid(seq),
        0 <= k <= seq.len() as int,
    ensures
        all_digits_1_2_3(seq, k),
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_input_implies_all_upto(seq, k - 1);
        assert(0 <= k - 1 && k - 1 < seq.len() as int);
        assert(1 <= seq[k - 1] as int <= 3);
    }
}

proof fn lemma_input_implies_all(seq: Seq<u8>)
    requires
        input_digits_valid(seq),
    ensures
        all_digits_1_2_3(seq, seq.len() as int),
{
    lemma_input_implies_all_upto(seq, seq.len() as int);
}

proof fn lemma_count_digit_all(seq: Seq<u8>, v: int, len: int)
    requires
        0 <= len <= seq.len(),
        forall|k: int| 0 <= k < len ==> seq[k] as int == v,
    ensures
        count_digit(seq, v, len) == len as nat,
    decreases len,
{
    if len <= 0 {
    } else {
        lemma_count_digit_all(seq, v, len - 1);
        reveal_with_fuel(count_digit, 2);
    }
}

proof fn lemma_count_digit_none(seq: Seq<u8>, v: int, len: int)
    requires
        0 <= len <= seq.len(),
        forall|k: int| 0 <= k < len ==> seq[k] as int != v,
    ensures
        count_digit(seq, v, len) == 0nat,
    decreases len,
{
    if len <= 0 {
    } else {
        lemma_count_digit_none(seq, v, len - 1);
        reveal_with_fuel(count_digit, 2);
    }
}

proof fn lemma_count_digit_step(seq: Seq<u8>, v: int, end: int)
    requires
        0 < end <= seq.len(),
    ensures
        count_digit(seq, v, end) == count_digit(seq, v, end - 1)
            + (if seq[end - 1] as int == v { 1nat } else { 0nat }),
    decreases end,
{
    reveal_with_fuel(count_digit, 2);
    if end > 1 {
        lemma_count_digit_step(seq, v, end - 1);
    }
}

proof fn lemma_count_digit_same_prefix(seq1: Seq<u8>, seq2: Seq<u8>, v: int, end: int)
    requires
        0 <= end <= seq1.len(),
        0 <= end <= seq2.len(),
        forall|i: int| 0 <= i < end ==> seq1[i] == seq2[i],
    ensures
        count_digit(seq1, v, end) == count_digit(seq2, v, end),
    decreases end,
{
    if end <= 0 {
    } else {
        lemma_count_digit_same_prefix(seq1, seq2, v, end - 1);
        reveal_with_fuel(count_digit, 2);
    }
}

impl Solution {
    pub fn sort_digits(nums: Vec<u8>) -> (res: Vec<u8>)
        requires
            1 <= nums.len() <= 100,
            input_digits_valid(nums@),
        ensures
            res@.len() == nums@.len(),
            sorted(res@),
            forall|v: int| 1 <= v <= 3 ==>
                count_digit(res@, v, res@.len() as int) == count_digit(nums@, v, nums@.len() as int),
    {
        let n = nums.len();
        proof {
            assert(input_digits_valid(nums@));
            lemma_input_implies_all(nums@);
        }
        let mut c1 = 0usize;
        let mut c2 = 0usize;
        let mut c3 = 0usize;
        let mut i = 0usize;
        while i < n
            invariant
                n == nums.len(),
                (nums@).len() == n as int,
                all_digits_1_2_3(nums@, n as int),
                i <= n,
                c1 + c2 + c3 == i,
                c1 as int == count_digit(nums@, 1, i as int),
                c2 as int == count_digit(nums@, 2, i as int),
                c3 as int == count_digit(nums@, 3, i as int),
            decreases n - i,
        {
            let ghost i_old = i;
            let ghost c1_old = c1;
            let ghost c2_old = c2;
            let ghost c3_old = c3;
            if nums[i] == 1 {
                c1 += 1;
            } else if nums[i] == 2 {
                c2 += 1;
            } else {
                c3 += 1;
            }
            i += 1;
            proof {
                lemma_count_digit_step(nums@, 1, i as int);
                lemma_count_digit_step(nums@, 2, i as int);
                lemma_count_digit_step(nums@, 3, i as int);
                assert(i as int == i_old as int + 1);
                if c1 as int == c1_old as int + 1 {
                    assert((nums@)[i_old as int] as int == 1);
                    assert(c1 as int == count_digit(nums@, 1, i as int));
                    assert(c2 as int == count_digit(nums@, 2, i as int));
                    assert(c3 as int == count_digit(nums@, 3, i as int));
                } else if c2 as int == c2_old as int + 1 {
                    assert((nums@)[i_old as int] as int == 2);
                    assert(c1 as int == count_digit(nums@, 1, i as int));
                    assert(c2 as int == count_digit(nums@, 2, i as int));
                    assert(c3 as int == count_digit(nums@, 3, i as int));
                } else {
                    assert(c3 as int == c3_old as int + 1);
                    lemma_all_digits_at(nums@, n as int, i_old as int);
                    assert((nums@)[i_old as int] as int != 1);
                    assert((nums@)[i_old as int] as int != 2);
                    assert((nums@)[i_old as int] as int == 3);
                    assert(c1 as int == count_digit(nums@, 1, i as int));
                    assert(c2 as int == count_digit(nums@, 2, i as int));
                    assert(c3 as int == count_digit(nums@, 3, i as int));
                }
            }
        }
        let mut res = Vec::new();
        let mut j = 0usize;
        while j < c1
            invariant
                j <= c1,
                res@.len() == j as int,
                forall|k: int| 0 <= k < j as int ==> res@[k] as int == 1,
            decreases c1 - j,
        {
            res.push(1u8);
            j += 1;
        }
        proof {
            assert(j == c1);
            assert(res@.len() == c1 as int);
            assert(forall|k: int| 0 <= k < c1 as int ==> res@[k] as int == 1);
            lemma_count_digit_all(res@, 1, c1 as int);
            assert(count_digit(res@, 1, res@.len() as int) == c1 as nat);
            lemma_count_digit_none(res@, 2, c1 as int);
            lemma_count_digit_none(res@, 3, c1 as int);
        }
        j = 0;
        while j < c2
            invariant
                j <= c2,
                res@.len() == c1 as int + j as int,
                count_digit(res@, 1, res@.len() as int) == c1 as nat,
                count_digit(res@, 2, res@.len() as int) == j as nat,
                count_digit(res@, 3, res@.len() as int) == 0nat,
                forall|i: int| 0 <= i < c1 as int ==> res@[i] as int == 1,
                forall|i: int| c1 as int <= i && i < c1 as int + j as int ==> res@[i] as int == 2,
            decreases c2 - j,
        {
            let ghost old_res = res@;
            res.push(2u8);
            j += 1;
            proof {
                assert(res@.len() as int == old_res.len() as int + 1);
                assert(forall|i: int| 0 <= i < old_res.len() as int ==> res@[i] == old_res[i]);
                lemma_count_digit_same_prefix(res@, old_res, 1, old_res.len() as int);
                lemma_count_digit_same_prefix(res@, old_res, 2, old_res.len() as int);
                lemma_count_digit_same_prefix(res@, old_res, 3, old_res.len() as int);
                assert(count_digit(res@, 1, old_res.len() as int) == c1 as nat);
                assert(count_digit(res@, 2, old_res.len() as int) == j as int - 1);
                lemma_count_digit_step(res@, 1, res@.len() as int);
                lemma_count_digit_step(res@, 2, res@.len() as int);
                lemma_count_digit_step(res@, 3, res@.len() as int);
            }
        }
        proof {
            assert(res@.len() == c1 as int + c2 as int);
            assert(count_digit(res@, 1, res@.len() as int) == c1 as nat);
            assert(count_digit(res@, 2, res@.len() as int) == c2 as nat);
            assert(count_digit(res@, 3, res@.len() as int) == 0nat);
        }
        j = 0;
        while j < c3
            invariant
                j <= c3,
                res@.len() == c1 as int + c2 as int + j as int,
                count_digit(res@, 1, res@.len() as int) == c1 as nat,
                count_digit(res@, 2, res@.len() as int) == c2 as nat,
                count_digit(res@, 3, res@.len() as int) == j as nat,
                forall|i: int| 0 <= i < c1 as int ==> res@[i] as int == 1,
                forall|i: int| c1 as int <= i && i < c1 as int + c2 as int ==> res@[i] as int == 2,
                forall|i: int| c1 as int + c2 as int <= i && i < c1 as int + c2 as int + j as int ==> res@[i] as int == 3,
            decreases c3 - j,
        {
            let ghost old_res = res@;
            res.push(3u8);
            j += 1;
            proof {
                assert(res@.len() as int == old_res.len() as int + 1);
                assert(forall|i: int| 0 <= i < old_res.len() as int ==> res@[i] == old_res[i]);
                lemma_count_digit_same_prefix(res@, old_res, 1, old_res.len() as int);
                lemma_count_digit_same_prefix(res@, old_res, 2, old_res.len() as int);
                lemma_count_digit_same_prefix(res@, old_res, 3, old_res.len() as int);
                assert(count_digit(res@, 1, old_res.len() as int) == c1 as nat);
                assert(count_digit(res@, 2, old_res.len() as int) == c2 as nat);
                assert(count_digit(res@, 3, old_res.len() as int) == j as int - 1);
                lemma_count_digit_step(res@, 1, res@.len() as int);
                lemma_count_digit_step(res@, 2, res@.len() as int);
                lemma_count_digit_step(res@, 3, res@.len() as int);
            }
        }
        proof {
            assert(c1 as int + c2 as int + c3 as int == n as int);
            assert(res@.len() == n as int);
            assert(count_digit(nums@, 1, n as int) == c1 as nat);
            assert(count_digit(nums@, 2, n as int) == c2 as nat);
            assert(count_digit(nums@, 3, n as int) == c3 as nat);
            assert(forall|v: int| 1 <= v <= 3 ==>
                count_digit(res@, v, res@.len() as int) == count_digit(nums@, v, nums@.len() as int));
            assert(forall|i: int| 0 <= i < c1 as int ==> res@[i] as int == 1);
            assert(forall|i: int| c1 as int <= i && i < c1 as int + c2 as int ==> res@[i] as int == 2);
            assert(forall|i: int| c1 as int + c2 as int <= i && i < res@.len() as int ==> res@[i] as int == 3);
            lemma_three_segment_sorted(res@, c1 as int, c2 as int, c3 as int);
        }
        res
    }
}

}
