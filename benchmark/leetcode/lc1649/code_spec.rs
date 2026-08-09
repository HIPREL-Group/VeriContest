use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_less(instructions: Seq<i32>, end: int, val: i32) -> int
    decreases end
{
    if end <= 0 { 0 }
    else if instructions[end - 1] < val {
        count_less(instructions, end - 1, val) + 1
    } else {
        count_less(instructions, end - 1, val)
    }
}

pub open spec fn count_greater(instructions: Seq<i32>, end: int, val: i32) -> int
    decreases end
{
    if end <= 0 { 0 }
    else if instructions[end - 1] > val {
        count_greater(instructions, end - 1, val) + 1
    } else {
        count_greater(instructions, end - 1, val)
    }
}

pub open spec fn min_spec(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn count_in_range(instructions: Seq<i32>, end: int, lo: int, hi: int) -> int
    decreases end
{
    if end <= 0 {
        0
    } else {
        count_in_range(instructions, end - 1, lo, hi)
            + (if lo <= instructions[end - 1] && instructions[end - 1] as int <= hi { 1int } else { 0int })
    }
}

pub open spec fn blocks_sum_upto(instructions: Seq<i32>, end: int, block_size: int, b: int) -> int
    decreases b
{
    if b <= 0 {
        0
    } else {
        blocks_sum_upto(instructions, end, block_size, b - 1)
            + count_in_range(instructions, end, (b - 1) * block_size + 1, min_spec(b * block_size, 100_000))
    }
}

pub open spec fn total_cost(instructions: Seq<i32>, n: int) -> int
    decreases n
{
    if n <= 0 { 0 }
    else {
        total_cost(instructions, n - 1) + min_spec(
            count_less(instructions, n - 1, instructions[n - 1]),
            count_greater(instructions, n - 1, instructions[n - 1])
        )
    }
}

impl Solution {
    pub fn create_sorted_array(instructions: Vec<i32>) -> (res: i32)
        requires
            1 <= instructions.len() <= 100_000,
            forall |i: int| 0 <= i < instructions.len() ==> 1 <= #[trigger] instructions[i] <= 100_000,
        ensures
            0 <= res < 1_000_000_007,
            res as int == total_cost(instructions@, instructions@.len() as int) % 1_000_000_007,
    {
        let mut cost: i64 = 0;
        let n = instructions.len();
        let block_size: usize = 320;
        let num_blocks: usize = 313;

        let mut freq: Vec<i64> = Vec::new();
        let mut fi: usize = 0;
        while fi < 100_000 {
            freq.push(0);
            fi = fi + 1;
        }

        let mut block_sum: Vec<i64> = Vec::new();
        let mut bi: usize = 0;
        while bi < num_blocks {
            block_sum.push(0);
            bi = bi + 1;
        }

        let mut i: usize = 0;
        while i < n {
            let val = instructions[i] as usize;
            let b0 = val / block_size;

            let mut sum: i64 = 0;
            let mut bb: usize = 0;
            while bb < b0 {
                sum = sum + block_sum[bb];
                bb = bb + 1;
            }

            let mut p: usize = b0 * block_size;
            while p < val {
                sum = sum + freq[p];
                p = p + 1;
            }
            let leq = sum;

            let less = leq - freq[val - 1];
            let greater = (i as i64) - leq;

            let min_cost: i64 = if less < greater { less } else { greater };
            cost = cost + min_cost;

            let pos = val - 1;
            freq.set(pos, freq[pos] + 1);
            let block_idx = pos / block_size;
            block_sum.set(block_idx, block_sum[block_idx] + 1);

            i = i + 1;
        }
        (cost % 1_000_000_007) as i32
    }
}

}
