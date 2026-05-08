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
        while len <= max_n {
            let prev = ways[len - 1];
            let current = len;
            let next = if len < k as usize {
                prev
            } else {
                Self::add_mod(prev, ways[len - k as usize])
            };
            let next_prefix = Self::add_mod(prefix[len - 1], next);
            ways.push(next);
            prefix.push(next_prefix);
            len += 1;
        }
        let mut answers = Vec::new();
        let mut idx = 0usize;
        while idx < lefts.len() {
            let left = lefts[idx];
            let right = rights[idx];
            let answer = if left == 1 {
                prefix[right as usize]
            } else {
                Self::sub_mod(prefix[right as usize], prefix[left as usize - 1])
            };
            answers.push(answer);
            idx += 1;
        }
        answers
    }
}

}
