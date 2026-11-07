use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn is_valley_at(a: Seq<i64>, n: usize, l: int, r: int) -> bool {
    0 <= l && l <= r && r < n &&
    (forall|i: int| l <= i && i <= r ==> a[i] == a[l]) &&
    (l == 0 || a[l - 1] > a[l]) &&
    (r == n - 1 || a[r] < a[r + 1])
}

pub open spec fn has_unique_valley(a: Seq<i64>, n: usize) -> bool {
    exists|l: int, r: int| #![auto]
        is_valley_at(a, n, l, r) &&
        forall|l2: int, r2: int| is_valley_at(a, n, l2, r2) ==> l2 == l && r2 == r
}

proof fn lemma_valley_ending_in_block_is_the_block(
    a: Seq<i64>,
    n: usize,
    block_start: int,
    block_end: int,
    l: int,
    r: int,
)
    requires
        0 <= block_start,
        block_start <= block_end,
        block_end < n as int,
        forall|j: int| block_start <= j && j <= block_end ==> a[j] == a[block_start],
        block_start == 0 || a[block_start - 1] != a[block_start],
        block_end == n as int - 1 || a[block_end] != a[block_end + 1],
        is_valley_at(a, n, l, r),
        block_start <= r,
        r <= block_end,
    ensures
        l == block_start,
        r == block_end,
{
    if l < block_start {
        assert(block_start > 0);
        assert(l <= block_start - 1 && block_start <= r);
        assert(a[block_start - 1] == a[l]);
        assert(a[block_start] == a[l]);
        assert(a[block_start - 1] == a[block_start]);
        assert(false);
    }
    if l > block_start {
        assert(block_start <= l - 1 && l - 1 < l && l <= block_end);
        assert(a[l - 1] == a[block_start]);
        assert(a[l] == a[block_start]);
        assert(a[l - 1] == a[l]);
        assert(a[l - 1] > a[l]);
        assert(false);
    }
    if r < block_end {
        assert(block_start <= r && r < r + 1 && r + 1 <= block_end);
        assert(a[r] == a[block_start]);
        assert(a[r + 1] == a[block_start]);
        assert(a[r] == a[r + 1]);
        assert(a[r] < a[r + 1]);
        assert(false);
    }
}

pub struct Solution;

impl Solution {
    pub fn is_valley(n: usize, a: Vec<i64>) -> (count: i64)
        requires
            1 <= n && n <= 200000,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= 1000000000,
        ensures
            count >= 0,
            count == 1 <==> has_unique_valley(a@, n),
    {
        let mut count: i64 = 0;
        let mut i: usize = 0;
        let ghost mut last_valley_l: int = -1;
        let ghost mut last_valley_r: int = -1;
        let ghost mut first_many_l: int = -1;
        let ghost mut first_many_r: int = -1;
        let ghost mut second_many_l: int = -1;
        let ghost mut second_many_r: int = -1;
        while i < n
            invariant
                0 <= i && i <= n,
                n <= 200000,
                a.len() == n,
                forall|j: int| 0 <= j && j < n ==> 1 <= a@[j] && a@[j] <= 1000000000,
                count >= 0 && count <= i as i64,
                0 < i && i < n ==> a@[i as int - 1] != a@[i as int],
                count == 0 ==> forall|l: int, r: int|
                    0 <= l && l <= r && r < i as int ==> !is_valley_at(a@, n, l, r),
                count == 1 ==> 0 <= last_valley_l && last_valley_l <= last_valley_r && last_valley_r < i as int &&
                    is_valley_at(a@, n, last_valley_l, last_valley_r) &&
                    forall|l: int, r: int|
                        0 <= l && l <= r && r < i as int && is_valley_at(a@, n, l, r) ==> l == last_valley_l && r == last_valley_r,
                count > 1 ==> 0 <= first_many_l && first_many_l <= first_many_r && first_many_r < i as int &&
                    0 <= second_many_l && second_many_l <= second_many_r && second_many_r < i as int &&
                    is_valley_at(a@, n, first_many_l, first_many_r) &&
                    is_valley_at(a@, n, second_many_l, second_many_r) &&
                    (first_many_l != second_many_l || first_many_r != second_many_r),
            decreases n - i
        {
            let block_start = i;
            while i < n && a[i] == a[block_start]
                invariant
                    block_start <= i && i <= n,
                    n <= 200000,
                    a.len() == n,
                    forall|j: int| 0 <= j && j < n ==> 1 <= a@[j] && a@[j] <= 1000000000,
                    forall|j: int| block_start as int <= j && j < i as int ==> a@[j] == a@[block_start as int],
                decreases n - i
            {
                i += 1;
            }
            let block_end = i - 1;
            let left_ok = block_start == 0 || a[block_start - 1] > a[block_start];
            let right_ok = block_end == n - 1 || a[block_end] < a[block_end + 1];
            proof {
                assert forall|j: int| block_start as int <= j && j <= block_end as int implies a@[j] == a@[block_start as int] by {
                    assert(block_start as int <= j && j < i as int);
                }
                if block_start > 0 {
                    assert(a@[block_start as int - 1] != a@[block_start as int]);
                }
                if block_end < n - 1 {
                    assert(a@[block_end as int + 1] != a@[block_end as int]);
                }
            }
            if left_ok && right_ok {
                let ghost prev_last_l = last_valley_l;
                let ghost prev_last_r = last_valley_r;
                proof {
                    assert(is_valley_at(a@, n, block_start as int, block_end as int));
                    last_valley_l = block_start as int;
                    last_valley_r = block_end as int;
                }
                count += 1;
                proof {
                    if count == 1 {
                        assert forall|l: int, r: int|
                            0 <= l && l <= r && r < i as int && is_valley_at(a@, n, l, r) implies l == last_valley_l && r == last_valley_r by {
                            if r < block_start as int {
                                assert(!is_valley_at(a@, n, l, r));
                            } else {
                                lemma_valley_ending_in_block_is_the_block(a@, n, block_start as int, block_end as int, l, r);
                            }
                        }
                    }
                    if count > 1 {
                        if count == 2 {
                            first_many_l = prev_last_l;
                            first_many_r = prev_last_r;
                            second_many_l = block_start as int;
                            second_many_r = block_end as int;
                            assert(prev_last_r < block_start as int);
                            assert(is_valley_at(a@, n, prev_last_l, prev_last_r));
                            assert(is_valley_at(a@, n, block_start as int, block_end as int));
                            assert(prev_last_l != block_start as int || prev_last_r != block_end as int);
                        }
                    }
                }
            } else {
                proof {
                    assert forall|l: int, r: int|
                        block_start as int <= r && r < i as int && is_valley_at(a@, n, l, r) implies false by {
                        lemma_valley_ending_in_block_is_the_block(a@, n, block_start as int, block_end as int, l, r);
                        assert(l == block_start as int && r == block_end as int);
                        assert(!(left_ok && right_ok));
                    }
                }
            }
        }
        proof {
            if count == 1 {
                assert(has_unique_valley(a@, n));
            }
            if has_unique_valley(a@, n) {
                if count == 0 {
                    assert(false);
                }
                if count > 1 {
                    let (ul, ur) = choose|l: int, r: int|
                        is_valley_at(a@, n, l, r) &&
                        forall|l2x: int, r2x: int| is_valley_at(a@, n, l2x, r2x) ==> l2x == l && r2x == r;
                    assert(first_many_l == ul && first_many_r == ur);
                    assert(second_many_l == ul && second_many_r == ur);
                    assert(first_many_l == second_many_l && first_many_r == second_many_r);
                    assert(false);
                }
                assert(count == 1);
            }
        }
        count
    }
}

}
