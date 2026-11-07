use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn segment_sum(s: Seq<i32>, start: int, len: int) -> int
    decreases len,
{
    if len <= 0 {
        0
    } else {
        s[start] as int + segment_sum(s, start + 1, len - 1)
    }
}

pub open spec fn segment_fits(books: Seq<i32>, start: int, len: int, t: int) -> bool
    recommends 0 <= start, 0 <= len, start + len <= books.len(),
{
    segment_sum(books, start, len) <= t
}

pub open spec fn any_segment_of_len_fits(books: Seq<i32>, len: int, t: int) -> bool
    recommends 0 <= len <= books.len(),
{
    exists|i: int| 0 <= i && i + len <= books.len() && segment_fits(books, i, len, t)
}

pub open spec fn segment_exceeds_time(books: Seq<i32>, start: int, right: int, t: int) -> bool
    recommends 0 <= start <= right <= books.len(),
{
    t < segment_sum(books, start, right - start)
}

pub open spec fn no_prefix_fit(books: Seq<i32>, left: int, right: int, t: int) -> bool
    recommends 0 <= left <= right <= books.len(),
{
    forall|i: int| 0 <= i && i < left ==> #[trigger] segment_exceeds_time(books, i, right, t)
}

proof fn segment_bounded(books: &Vec<i32>, start: int, len: int)
    requires
        0 <= start,
        start + len <= books@.len(),
        forall|i: int| 0 <= i < books@.len() ==> 1 <= #[trigger] books@[i] <= 10_000,
    ensures
        forall|j: int| start <= j < start + len ==> 1 <= #[trigger] books@[j] <= 10_000,
{
}

proof fn books_nonneg(books: &Vec<i32>)
    requires
        forall|i: int| 0 <= i < books@.len() ==> 1 <= #[trigger] books@[i] <= 10_000,
    ensures
        forall|j: int| 0 <= j < books@.len() ==> 0 <= #[trigger] books@[j] as int,
{
}

proof fn lemma_segment_sum_bounds(s: Seq<i32>, start: int, len: int)
    requires
        0 <= start,
        0 <= len,
        start + len <= s.len(),
        forall|j: int| start <= j < start + len ==> 1 <= #[trigger] s[j] <= 10_000,
    ensures
        0 <= segment_sum(s, start, len),
        segment_sum(s, start, len) <= len * 10_000,
    decreases len,
{
    if len == 0 {
        reveal_with_fuel(segment_sum, 1);
    } else {
        reveal_with_fuel(segment_sum, 2);
        lemma_segment_sum_bounds(s, start + 1, len - 1);
    }
}

proof fn lemma_segment_sum_ge_first(s: Seq<i32>, start: int, len: int)
    requires
        0 <= start,
        1 <= len,
        start + len <= s.len(),
        forall|j: int| 0 <= j < s.len() ==> 0 <= #[trigger] s[j] as int,
    ensures
        segment_sum(s, start, len) >= s[start] as int,
    decreases len,
{
    reveal_with_fuel(segment_sum, 2);
    if len == 1 {
    } else {
        lemma_segment_sum_ge_first(s, start + 1, len - 1);
    }
}

proof fn lemma_segment_sum_step(s: Seq<i32>, start: int, len: int)
    requires
        0 <= start,
        1 <= len,
        start + len <= s.len(),
    ensures
        segment_sum(s, start, len) == segment_sum(s, start, len - 1) + s[start + len - 1] as int,
    decreases len,
{
    if len == 1 {
        reveal_with_fuel(segment_sum, 2);
    } else {
        reveal_with_fuel(segment_sum, 2);
        lemma_segment_sum_step(s, start + 1, len - 1);
    }
}

proof fn lemma_segment_sum_split(s: Seq<i32>, start: int, prefix_len: int, suffix_len: int)
    requires
        0 <= start,
        0 <= prefix_len,
        0 <= suffix_len,
        start + prefix_len + suffix_len <= s.len(),
    ensures
        segment_sum(s, start, prefix_len + suffix_len)
            == segment_sum(s, start, prefix_len) + segment_sum(s, start + prefix_len, suffix_len),
    decreases prefix_len,
{
    if prefix_len == 0 {
        reveal_with_fuel(segment_sum, 1);
    } else {
        reveal_with_fuel(segment_sum, 2);
        lemma_segment_sum_split(s, start + 1, prefix_len - 1, suffix_len);
    }
}

proof fn lemma_segment_sum_prefix(s: Seq<i32>, start: int, len: int, i: int)
    requires
        0 <= start,
        0 <= i <= len,
        start + len <= s.len(),
        forall|j: int| 0 <= j < s.len() ==> 1 <= #[trigger] s[j] <= 10_000,
    ensures
        segment_sum(s, start, i) <= segment_sum(s, start, len),
    decreases len - i,
{
    if i == len {
    } else {
        lemma_segment_sum_step(s, start, i + 1);
        assert(segment_sum(s, start, i + 1) == segment_sum(s, start, i) + s[start + i] as int);
        assert(s[start + i] as int >= 1);
        assert(segment_sum(s, start, i) <= segment_sum(s, start, i + 1));
        lemma_segment_sum_prefix(s, start, len, i + 1);
    }
}

impl Solution {
    pub fn max_books_read(books: Vec<i32>, t: i64) -> (result: usize)
        requires
            1 <= books.len() <= 100_000,
            1 <= t <= 1_000_000_000,
            forall|i: int| 0 <= i < books@.len() ==> 1 <= #[trigger] books@[i] <= 10_000,
        ensures
            (result as int) <= books@.len(),
            0 <= (result as int),
            exists|i: int|
                0 <= i && i + (result as int) <= books@.len()
                    && segment_fits(books@, i, result as int, t as int),
            forall|k: int|
                (result as int) < k && k <= books@.len() ==> !#[trigger] any_segment_of_len_fits(books@, k, t as int),
    {
        proof {
            assert(forall|i: int| 0 <= i < books@.len() ==> 1 <= #[trigger] books@[i] <= 10_000);
        }
        let n = books.len();
        let mut left: usize = 0;
        let mut right: usize = 0;
        let mut sum: i64 = 0;
        let mut best: usize = 0;
        let ghost mut witness_start: int = 0;
        while right < n
            invariant
                n == books.len(),
                1 <= t <= 1_000_000_000,
                right <= n,
                left <= right,
                left <= n,
                0 <= sum as int,
                sum as int == segment_sum(books@, left as int, (right - left) as int),
                sum as int <= t as int,
                sum as int <= (right - left) as int * 10_000,
                0 <= witness_start <= n,
                witness_start + (best as int) <= n,
                segment_fits(books@, witness_start, best as int, t as int),
                forall|i: int| 0 <= i < books@.len() ==> 1 <= #[trigger] books@[i] <= 10_000,
                no_prefix_fit(books@, left as int, right as int, t as int),
                forall|i: int, len: int|
                    0 <= i && 0 <= len && i + len <= right && len <= books@.len() && segment_fits(books@, i, len, t as int)
                        ==> len <= (best as int),
            decreases n - right,
        {
            proof {
                assert(sum as int == segment_sum(books@, left as int, (right - left) as int));
            }
            let ghost old_right = right as int;
            let ghost old_sum = sum;
            proof {
                assert(sum <= t);
                assert(t <= 1_000_000_000i64);
                assert(books@[right as int] as int <= 10_000);
                assert(sum + books@[right as int] as i64 <= 1_000_010_000i64);
            }
            sum = sum + books[right] as i64;
            right += 1;
            proof {
                assert((right - left) as int - 1 == old_right - left as int);
                assert(old_sum as int == segment_sum(books@, left as int, old_right - left as int));
                lemma_segment_sum_step(books@, left as int, (right - left) as int);
                assert(segment_sum(books@, left as int, (right - left) as int)
                    == segment_sum(books@, left as int, (right - left) as int - 1)
                        + books@[left as int + (right - left) as int - 1] as int);
                assert(left as int + (right - left) as int - 1 == old_right);
                assert(sum as int == segment_sum(books@, left as int, (right - left) as int));
                segment_bounded(&books, left as int, (right - left) as int);
                lemma_segment_sum_bounds(books@, left as int, (right - left) as int);
                assert(no_prefix_fit(books@, left as int, right as int, t as int)) by {
                    assert forall|i: int|
                        0 <= i && i < left ==> #[trigger] segment_exceeds_time(books@, i, right as int, t as int) by {
                        if 0 <= i && i < left {
                            lemma_segment_sum_step(books@, i, right as int - i);
                            assert(segment_sum(books@, i, right as int - i)
                                == segment_sum(books@, i, old_right - i) + books@[old_right] as int);
                            assert(no_prefix_fit(books@, left as int, old_right, t as int));
                            assert(segment_exceeds_time(books@, i, old_right, t as int));
                            assert(1 <= books@[old_right]);
                            assert(segment_exceeds_time(books@, i, right as int, t as int));
                        }
                    }
                }
            }
            while sum > t && left < right
                invariant
                    n == books.len(),
                    1 <= t <= 1_000_000_000,
                    left < right ==> left <= n,
                    left <= right,
                    right <= n,
                    left <= n,
                    left < right ==> (right - left) as int >= 1,
                    sum as int == segment_sum(books@, left as int, (right - left) as int),
                    0 <= sum as int,
                    sum as int <= (right - left) as int * 10_000,
                    forall|i: int| 0 <= i < books@.len() ==> 1 <= #[trigger] books@[i] <= 10_000,
                    no_prefix_fit(books@, left as int, right as int, t as int),
                    forall|i: int, len: int|
                        0 <= i && 0 <= len && i + len < right && len <= books@.len() && segment_fits(books@, i, len, t as int)
                            ==> len <= (best as int),
                decreases right - left,
            {
                proof {
                    assert((right - left) as int >= 1);
                    lemma_segment_sum_step(books@, left as int, (right - left) as int);
                }
                let ghost old_left = left as int;
                let ghost old_sum_inner = sum as int;
                proof {
                    books_nonneg(&books);
                    lemma_segment_sum_ge_first(books@, left as int, (right - left) as int);
                }
                sum = sum - books[left] as i64;
                left += 1;
                proof {
                    reveal_with_fuel(segment_sum, 2);
                    assert(segment_sum(books@, old_left, (right as int - old_left))
                        == books@[old_left] as int
                            + segment_sum(books@, old_left + 1, (right as int - old_left - 1) as int));
                    assert(left as int == old_left + 1);
                    assert((right - left) as int == (right as int - old_left - 1) as int);
                    assert(sum as int == segment_sum(books@, left as int, (right - left) as int));
                    segment_bounded(&books, left as int, (right - left) as int);
                    lemma_segment_sum_bounds(books@, left as int, (right - left) as int);
                    assert(no_prefix_fit(books@, left as int, right as int, t as int)) by {
                        assert forall|i: int|
                            0 <= i && i < left ==> #[trigger] segment_exceeds_time(books@, i, right as int, t as int) by {
                            if 0 <= i && i < left {
                                if i < old_left {
                                    assert(no_prefix_fit(books@, old_left, right as int, t as int));
                                    assert(segment_exceeds_time(books@, i, right as int, t as int));
                                } else {
                                    assert(i == old_left);
                                    assert(old_sum_inner == segment_sum(books@, i, right as int - i));
                                    assert(old_sum_inner > t as int);
                                    assert(segment_exceeds_time(books@, i, right as int, t as int));
                                }
                            }
                        }
                    }
                }
            }
            if right - left > best {
                best = right - left;
                proof {
                    witness_start = left as int;
                    assert(segment_sum(books@, left as int, (right - left) as int) == sum as int);
                    assert(sum <= t);
                    assert(segment_fits(books@, witness_start, best as int, t as int));
                }
            }
            proof {
                assert forall|i: int, len: int|
                    0 <= i && 0 <= len && i + len <= right && len <= books@.len() && segment_fits(books@, i, len, t as int)
                    implies len <= (best as int) by {
                    if i + len < right {
                    } else {
                        assert(i + len == right);
                        assert(len >= 0);
                        assert(i >= left as int) by {
                            if i < left {
                                assert(no_prefix_fit(books@, left as int, right as int, t as int));
                                assert(segment_exceeds_time(books@, i, right as int, t as int));
                                assert(len == right as int - i);
                            }
                        }
                        assert((right - left) as int >= len) by {
                            assert(i >= left as int);
                            assert(right as int == i + len);
                            assert((right - left) as int == (i + len - left) as int);
                            assert(i >= left as int);
                        }
                        assert(best as int >= (right - left) as int);
                    }
                }
            }
        }
        proof {
            assert(segment_fits(books@, witness_start, best as int, t as int));
            assert forall|k: int|
                (best as int) < k && k <= books@.len() implies !#[trigger] any_segment_of_len_fits(books@, k, t as int)
                by {
                if (best as int) < k && k <= books@.len() {
                    assert(any_segment_of_len_fits(books@, k, t as int) ==> (best as int) >= k) by {
                        if any_segment_of_len_fits(books@, k, t as int) {
                            let i = choose|i: int| 0 <= i && i + k <= books@.len() && segment_fits(books@, i, k, t as int);
                            assert(0 <= i && i + k <= books@.len() && segment_fits(books@, i, k, t as int));
                        }
                    }
                    assert(!any_segment_of_len_fits(books@, k, t as int));
                }
            }
        }
        best
    }
}

}
