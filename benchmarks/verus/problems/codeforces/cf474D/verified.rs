use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn modulus() -> int {
    1_000_000_007
}

pub open spec fn sum_blocks(blocks: Seq<int>) -> int
    decreases blocks.len(),
{
    if blocks.len() == 0 {
        0
    } else {
        sum_blocks(blocks.drop_last()) + blocks[blocks.len() - 1]
    }
}

pub open spec fn valid_dinner_blocks(blocks: Seq<int>, total: int, k: int) -> bool
    recommends
        0 <= total,
        1 <= k,
{
    &&& sum_blocks(blocks) == total
    &&& forall|i: int| 0 <= i < blocks.len() ==> blocks[i] == 1 || blocks[i] == k
}

pub open spec fn count_valid_dinners(total: nat, k: nat) -> int
    recommends
        1 <= k,
    decreases total,
{
    if total == 0 {
        1
    } else if k == 0 {
        0
    } else if total < k {
        count_valid_dinners((total - 1) as nat, k)
    } else {
        count_valid_dinners((total - 1) as nat, k) + count_valid_dinners((total - k) as nat, k)
    }
}

pub open spec fn count_valid_dinners_up_to(total: nat, k: nat) -> int
    recommends
        1 <= k,
    decreases total,
{
    if total == 0 {
        0
    } else {
        count_valid_dinners_up_to((total - 1) as nat, k) + count_valid_dinners(total, k)
    }
}

pub open spec fn query_answer(left: int, right: int, k: int) -> int
    recommends
        1 <= left <= right,
        1 <= k,
{
    (count_valid_dinners_up_to(right as nat, k as nat) - count_valid_dinners_up_to((left - 1) as nat, k as nat)) % modulus()
}

pub open spec fn count_valid_dinners_mod(total: nat, k: nat) -> int
    recommends
        1 <= k,
    decreases total,
{
    if total == 0 {
        1
    } else if k == 0 {
        0
    } else if total < k {
        count_valid_dinners_mod((total - 1) as nat, k)
    } else {
        (count_valid_dinners_mod((total - 1) as nat, k) + count_valid_dinners_mod((total - k) as nat, k)) % modulus()
    }
}

pub open spec fn count_valid_dinners_up_to_mod(total: nat, k: nat) -> int
    recommends
        1 <= k,
    decreases total,
{
    if total == 0 {
        0
    } else {
        (count_valid_dinners_up_to_mod((total - 1) as nat, k) + count_valid_dinners_mod(total, k)) % modulus()
    }
}

pub open spec fn sub_mod_int(x: int, y: int) -> int
    recommends
        0 <= x < modulus(),
        0 <= y < modulus(),
{
    if x >= y {
        x - y
    } else {
        x + modulus() - y
    }
}

pub open spec fn query_answer_mod(left: int, right: int, k: int) -> int
    recommends
        1 <= left <= right,
        1 <= k,
{
    if left == 1 {
        count_valid_dinners_up_to_mod(right as nat, k as nat)
    } else {
        sub_mod_int(count_valid_dinners_up_to_mod(right as nat, k as nat), count_valid_dinners_up_to_mod((left - 1) as nat, k as nat))
    }
}

proof fn lemma_count_valid_dinners_nonnegative(total: nat, k: nat)
    requires
        1 <= k,
    ensures
        0 <= count_valid_dinners(total, k),
    decreases total,
{
    if total > 0 {
        lemma_count_valid_dinners_nonnegative((total - 1) as nat, k);
        if total >= k {
            lemma_count_valid_dinners_nonnegative((total - k) as nat, k);
        }
    }
}

proof fn lemma_count_valid_dinners_up_to_nonnegative(total: nat, k: nat)
    requires
        1 <= k,
    ensures
        0 <= count_valid_dinners_up_to(total, k),
    decreases total,
{
    if total > 0 {
        lemma_count_valid_dinners_up_to_nonnegative((total - 1) as nat, k);
        lemma_count_valid_dinners_nonnegative(total, k);
    }
}

proof fn lemma_mod_add(x: int, y: int)
    requires
        0 <= x,
        0 <= y,
    ensures
        ((x % modulus()) + (y % modulus())) % modulus() == (x + y) % modulus(),
{
}

proof fn lemma_mod_sub(x: int, y: int)
    requires
        0 <= y <= x,
    ensures
        sub_mod_int(x % modulus(), y % modulus()) == (x - y) % modulus(),
{
}

proof fn lemma_count_valid_dinners_mod_correct(total: nat, k: nat)
    requires
        1 <= k,
    ensures
        count_valid_dinners_mod(total, k) == count_valid_dinners(total, k) % modulus(),
        0 <= count_valid_dinners_mod(total, k) < modulus(),
    decreases total,
{
    lemma_count_valid_dinners_nonnegative(total, k);
    if total > 0 {
        lemma_count_valid_dinners_mod_correct((total - 1) as nat, k);
        if total >= k {
            lemma_count_valid_dinners_mod_correct((total - k) as nat, k);
            lemma_count_valid_dinners_nonnegative((total - 1) as nat, k);
            lemma_count_valid_dinners_nonnegative((total - k) as nat, k);
            assert(0 <= count_valid_dinners((total - 1) as nat, k));
            assert(0 <= count_valid_dinners((total - k) as nat, k));
            lemma_mod_add(count_valid_dinners((total - 1) as nat, k), count_valid_dinners((total - k) as nat, k));
        }
    }
}

proof fn lemma_count_valid_dinners_up_to_monotone(start: nat, end: nat, k: nat)
    requires
        start <= end,
        1 <= k,
    ensures
        count_valid_dinners_up_to(start, k) <= count_valid_dinners_up_to(end, k),
    decreases end - start,
{
    if start < end {
        lemma_count_valid_dinners_up_to_monotone(start, (end - 1) as nat, k);
        lemma_count_valid_dinners_nonnegative(end, k);
    }
}

proof fn lemma_count_valid_dinners_up_to_mod_correct(total: nat, k: nat)
    requires
        1 <= k,
    ensures
        count_valid_dinners_up_to_mod(total, k) == count_valid_dinners_up_to(total, k) % modulus(),
        0 <= count_valid_dinners_up_to_mod(total, k) < modulus(),
    decreases total,
{
    if total > 0 {
        lemma_count_valid_dinners_up_to_mod_correct((total - 1) as nat, k);
        lemma_count_valid_dinners_mod_correct(total, k);
        lemma_count_valid_dinners_up_to_nonnegative((total - 1) as nat, k);
        lemma_count_valid_dinners_nonnegative(total, k);
        lemma_mod_add(count_valid_dinners_up_to((total - 1) as nat, k), count_valid_dinners(total, k));
    }
}

proof fn lemma_query_answer_mod_correct(left: int, right: int, k: int)
    requires
        1 <= left <= right,
        1 <= k,
    ensures
        query_answer_mod(left, right, k) == query_answer(left, right, k),
        0 <= query_answer_mod(left, right, k) < modulus(),
{
    lemma_count_valid_dinners_up_to_mod_correct(right as nat, k as nat);
    if left == 1 {
    } else {
        lemma_count_valid_dinners_up_to_mod_correct((left - 1) as nat, k as nat);
        lemma_count_valid_dinners_up_to_nonnegative((left - 1) as nat, k as nat);
        lemma_count_valid_dinners_up_to_monotone((left - 1) as nat, right as nat, k as nat);
        lemma_mod_sub(count_valid_dinners_up_to(right as nat, k as nat), count_valid_dinners_up_to((left - 1) as nat, k as nat));
    }
}

impl Solution {
    fn add_mod(x: i32, y: i32) -> (res: i32)
        requires
            0 <= x < modulus(),
            0 <= y < modulus(),
        ensures
            0 <= res < modulus(),
            res as int == ((x as int) + (y as int)) % modulus(),
    {
        let sum = x + y;
        if sum >= 1_000_000_007i32 {
            sum - 1_000_000_007i32
        } else {
            sum
        }
    }

    fn sub_mod(x: i32, y: i32) -> (res: i32)
        requires
            0 <= x < modulus(),
            0 <= y < modulus(),
        ensures
            0 <= res < modulus(),
            res as int == sub_mod_int(x as int, y as int),
    {
        if x >= y {
            x - y
        } else {
            x + 1_000_000_007i32 - y
        }
    }

    pub fn solve_queries(k: i32, lefts: Vec<i32>, rights: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= k <= 100_000,
            1 <= lefts.len() == rights.len() <= 100_000,
            forall|i: int|
                0 <= i < lefts.len() ==> 1 <= #[trigger] lefts[i] <= rights[i] <= 100_000,
        ensures
            res.len() == lefts.len(),
            forall|i: int|
                0 <= i < res.len() ==> 0 <= #[trigger] res[i] < modulus()
                    && res[i] as int == query_answer(lefts[i] as int, rights[i] as int, k as int),
    {
        let max_n = 100_000usize;
        let mut ways = Vec::new();
        ways.push(1);
        let mut prefix = Vec::new();
        prefix.push(0);
        let mut len = 1usize;
        while len <= max_n
            invariant
                1 <= k <= 100_000,
                1 <= lefts.len() == rights.len() <= 100_000,
                forall|i: int|
                    0 <= i < lefts.len() ==> 1 <= #[trigger] lefts[i] <= rights[i] <= 100_000,
                max_n == 100_000usize,
                ways.len() == len,
                prefix.len() == len,
                1 <= len <= max_n + 1,
                forall|j: int|
                    0 <= j < len ==> 0 <= #[trigger] ways[j] < modulus()
                        && ways[j] as int == count_valid_dinners_mod(j as nat, k as nat),
                forall|j: int|
                    0 <= j < len ==> 0 <= #[trigger] prefix[j] < modulus()
                        && prefix[j] as int == count_valid_dinners_up_to_mod(j as nat, k as nat),
            decreases max_n + 1 - len,
        {
            let prev = ways[len - 1];
            let current = len;
            let next = if len < k as usize {
                prev
            } else {
                Self::add_mod(prev, ways[len - k as usize])
            };
            let next_prefix = Self::add_mod(prefix[len - 1], next);
            proof {
                lemma_count_valid_dinners_mod_correct(current as nat, k as nat);
                lemma_count_valid_dinners_up_to_mod_correct(current as nat, k as nat);
            }
            let ghost old_ways = ways@;
            let ghost old_prefix = prefix@;
            ways.push(next);
            prefix.push(next_prefix);
            len += 1;
            proof {
                assert(ways@ == old_ways.push(next));
                assert(prefix@ == old_prefix.push(next_prefix));
                assert forall|j: int|
                    0 <= j < len implies 0 <= #[trigger] ways[j] < modulus()
                        && ways[j] as int == count_valid_dinners_mod(j as nat, k as nat) by {
                    if j == current as int {
                        if current < k as usize {
                            assert(next == prev);
                        } else {
                            assert(next as int == ((prev as int) + (ways[current - k as usize] as int)) % modulus());
                        }
                    } else {
                        assert(j < current as int);
                        assert(ways[j] == old_ways[j]);
                    }
                }
                assert forall|j: int|
                    0 <= j < len implies 0 <= #[trigger] prefix[j] < modulus()
                        && prefix[j] as int == count_valid_dinners_up_to_mod(j as nat, k as nat) by {
                    if j == current as int {
                        assert(next_prefix as int == ((prefix[current - 1] as int) + (next as int)) % modulus());
                    } else {
                        assert(j < current as int);
                        assert(prefix[j] == old_prefix[j]);
                    }
                }
            }
        }
        let mut answers = Vec::new();
        let mut idx = 0usize;
        while idx < lefts.len()
            invariant
                1 <= k <= 100_000,
                1 <= lefts.len() == rights.len() <= 100_000,
                forall|i: int|
                    0 <= i < lefts.len() ==> 1 <= #[trigger] lefts[i] <= rights[i] <= 100_000,
                max_n == 100_000usize,
                prefix.len() == max_n + 1,
                forall|j: int|
                    0 <= j < prefix.len() ==> 0 <= #[trigger] prefix[j] < modulus()
                        && prefix[j] as int == count_valid_dinners_up_to_mod(j as nat, k as nat),
                idx <= lefts.len(),
                answers.len() == idx,
                forall|j: int|
                    0 <= j < answers.len() ==> 0 <= #[trigger] answers[j] < modulus()
                        && answers[j] as int == query_answer(lefts[j] as int, rights[j] as int, k as int),
            decreases lefts.len() - idx,
        {
            let left = lefts[idx];
            let right = rights[idx];
            proof {
                assert(1 <= lefts[idx as int] <= rights[idx as int] <= 100_000);
                lemma_query_answer_mod_correct(left as int, right as int, k as int);
                assert(right <= 100_000);
                assert(max_n == 100_000usize);
                assert(prefix.len() == max_n + 1);
                assert((right as usize) < prefix.len());
                if left > 1 {
                    assert(left <= 100_000);
                    assert((left as usize) - 1 < prefix.len());
                }
            }
            let answer = if left == 1 {
                prefix[right as usize]
            } else {
                Self::sub_mod(prefix[right as usize], prefix[left as usize - 1])
            };
            let ghost old_answers = answers@;
            answers.push(answer);
            idx += 1;
            proof {
                assert(answers@ == old_answers.push(answer));
                assert forall|j: int|
                    0 <= j < answers.len() implies 0 <= #[trigger] answers[j] < modulus()
                        && answers[j] as int == query_answer(lefts[j] as int, rights[j] as int, k as int) by {
                    if j == idx as int - 1 {
                        if left == 1 {
                            assert(answer == prefix[right as int]);
                            assert(answer as int == query_answer_mod(left as int, right as int, k as int));
                        } else {
                            assert(answer as int == sub_mod_int(prefix[right as int] as int, prefix[left as int - 1] as int));
                            assert(answer as int == query_answer_mod(left as int, right as int, k as int));
                        }
                        assert(query_answer_mod(left as int, right as int, k as int) == query_answer(left as int, right as int, k as int));
                    } else {
                        assert(j < idx as int - 1);
                        assert(answers[j] == old_answers[j]);
                    }
                }
            }
        }
        answers
    }
}

}
