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

impl Solution {
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
    }
}

}
