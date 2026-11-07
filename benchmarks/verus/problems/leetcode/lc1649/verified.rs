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

proof fn count_less_eq_range(instructions: Seq<i32>, end: int, val: i32)
    requires
        0 <= end <= instructions.len(),
        forall |i: int| 0 <= i < instructions.len() ==> 1 <= #[trigger] instructions[i],
    ensures count_less(instructions, end, val) == count_in_range(instructions, end, 1, val as int - 1),
    decreases end
{
    if end > 0 {
        count_less_eq_range(instructions, end - 1, val);
    }
}

proof fn count_greater_eq_range(instructions: Seq<i32>, end: int, val: i32)
    requires
        0 <= end <= instructions.len(),
        forall |i: int| 0 <= i < instructions.len() ==> #[trigger] instructions[i] <= 100_000,
    ensures count_greater(instructions, end, val) == count_in_range(instructions, end, val as int + 1, 100_000),
    decreases end
{
    if end > 0 {
        count_greater_eq_range(instructions, end - 1, val);
    }
}

proof fn count_in_range_split(instructions: Seq<i32>, end: int, lo: int, mid: int, hi: int)
    requires 0 <= end <= instructions.len(), lo <= mid + 1, mid <= hi,
    ensures count_in_range(instructions, end, lo, hi)
        == count_in_range(instructions, end, lo, mid) + count_in_range(instructions, end, mid + 1, hi),
    decreases end
{
    if end > 0 {
        count_in_range_split(instructions, end - 1, lo, mid, hi);
        let x = instructions[end - 1];
        if lo <= x && x as int <= hi {
            if x as int <= mid {
                assert(lo <= x && x as int <= mid);
                assert(!(mid + 1 <= x && x as int <= hi));
            } else {
                assert(mid + 1 <= x && x as int <= hi);
                assert(!(lo <= x && x as int <= mid));
            }
        } else {
            assert(!(lo <= x && x as int <= mid));
            assert(!(mid + 1 <= x && x as int <= hi));
        }
    }
}

proof fn count_in_range_step(instructions: Seq<i32>, end: int, lo: int, hi: int)
    requires 0 <= end < instructions.len(),
    ensures count_in_range(instructions, end + 1, lo, hi)
        == count_in_range(instructions, end, lo, hi)
            + (if lo <= instructions[end] && instructions[end] as int <= hi { 1int } else { 0int }),
{
}

proof fn count_in_range_nonneg(instructions: Seq<i32>, end: int, lo: int, hi: int)
    requires 0 <= end <= instructions.len(),
    ensures 0 <= count_in_range(instructions, end, lo, hi) <= end,
    decreases end
{
    if end > 0 {
        count_in_range_nonneg(instructions, end - 1, lo, hi);
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

proof fn blocks_sum_upto_bound(instructions: Seq<i32>, end: int, block_size: int, b: int)
    requires 0 <= end <= instructions.len(), block_size >= 1, 0 <= b,
    ensures 0 <= blocks_sum_upto(instructions, end, block_size, b) <= end,
{
    blocks_sum_upto_eq(instructions, end, block_size, b);
    count_in_range_nonneg(instructions, end, 1, min_spec(b * block_size, 100_000));
}

proof fn blocks_sum_upto_eq(instructions: Seq<i32>, end: int, block_size: int, b: int)
    requires
        0 <= end <= instructions.len(),
        block_size >= 1,
        0 <= b,
    ensures blocks_sum_upto(instructions, end, block_size, b) == count_in_range(instructions, end, 1, min_spec(b * block_size, 100_000)),
    decreases b
{
    if b <= 0 {
        assert(b * block_size == 0) by (nonlinear_arith)
            requires b == 0;
        count_in_range_empty(instructions, end, 1, min_spec(b * block_size, 100_000));
    } else {
        blocks_sum_upto_eq(instructions, end, block_size, b - 1);
        assert((b - 1) * block_size <= b * block_size) by (nonlinear_arith)
            requires b >= 1, block_size >= 1;
        assert((b - 1) * block_size + block_size == b * block_size) by (nonlinear_arith)
            requires b >= 1;
        if (b - 1) * block_size < 100_000 {
            assert((b - 1) * block_size <= min_spec(b * block_size, 100_000));
            assert((b - 1) * block_size >= 0) by (nonlinear_arith)
                requires b >= 1, block_size >= 1;
            count_in_range_split(instructions, end, 1, (b - 1) * block_size, min_spec(b * block_size, 100_000));
        } else {
            assert(count_in_range(instructions, end, (b - 1) * block_size + 1, min_spec(b * block_size, 100_000)) == 0) by {
                assert((b - 1) * block_size + 1 > min_spec(b * block_size, 100_000));
                count_in_range_empty(instructions, end, (b - 1) * block_size + 1, min_spec(b * block_size, 100_000));
            }
        }
    }
}

proof fn count_in_range_empty(instructions: Seq<i32>, end: int, lo: int, hi: int)
    requires 0 <= end <= instructions.len(), lo > hi,
    ensures count_in_range(instructions, end, lo, hi) == 0,
    decreases end
{
    if end > 0 {
        count_in_range_empty(instructions, end - 1, lo, hi);
    }
}

proof fn count_in_range_all(instructions: Seq<i32>, end: int)
    requires
        0 <= end <= instructions.len(),
        forall |k: int| 0 <= k < instructions.len() ==> 1 <= #[trigger] instructions[k] <= 100_000,
    ensures count_in_range(instructions, end, 1, 100_000) == end,
    decreases end
{
    if end > 0 {
        count_in_range_all(instructions, end - 1);
    }
}

proof fn block_membership_excl(pos: int, block_size: int, bbb: int)
    requires block_size >= 1, 0 <= pos, bbb != pos / block_size,
    ensures !(bbb * block_size <= pos < (bbb + 1) * block_size),
{
    let q = pos / block_size;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(pos, block_size);
    vstd::arithmetic::div_mod::lemma_mod_bound(pos, block_size);
    assert(pos == block_size * q + pos % block_size);
    assert(0 <= pos % block_size < block_size);
    if bbb < q {
        assert((bbb + 1) * block_size <= q * block_size) by (nonlinear_arith)
            requires bbb + 1 <= q, block_size >= 1;
        assert(pos >= (bbb + 1) * block_size);
    } else {
        assert(bbb * block_size >= (q + 1) * block_size) by (nonlinear_arith)
            requires bbb >= q + 1, block_size >= 1;
        assert(block_size * q + block_size == (q + 1) * block_size) by (nonlinear_arith);
        assert(pos < (q + 1) * block_size);
        assert(pos < bbb * block_size);
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

proof fn count_less_bounds(instructions: Seq<i32>, end: int, val: i32)
    requires 0 <= end <= instructions.len()
    ensures 0 <= count_less(instructions, end, val) <= end
    decreases end
{
    if end > 0 {
        count_less_bounds(instructions, end - 1, val);
    }
}

proof fn count_greater_bounds(instructions: Seq<i32>, end: int, val: i32)
    requires 0 <= end <= instructions.len()
    ensures 0 <= count_greater(instructions, end, val) <= end
    decreases end
{
    if end > 0 {
        count_greater_bounds(instructions, end - 1, val);
    }
}

proof fn total_cost_nonneg(instructions: Seq<i32>, n: int)
    requires 0 <= n <= instructions.len()
    ensures total_cost(instructions, n) >= 0
    decreases n
{
    if n > 0 {
        total_cost_nonneg(instructions, n - 1);
        count_less_bounds(instructions, n - 1, instructions[n - 1]);
        count_greater_bounds(instructions, n - 1, instructions[n - 1]);
    }
}

proof fn total_cost_bound(instructions: Seq<i32>, n: int)
    requires 0 <= n <= instructions.len()
    ensures total_cost(instructions, n) <= n * n
    decreases n
{
    if n > 0 {
        total_cost_bound(instructions, n - 1);
        count_less_bounds(instructions, n - 1, instructions[n - 1]);
        count_greater_bounds(instructions, n - 1, instructions[n - 1]);
        assert((n - 1) * (n - 1) + (n - 1) <= n * n) by(nonlinear_arith)
            requires n > 0;
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
        while fi < 100_000
            invariant
                freq@.len() == fi as int,
                0 <= fi <= 100_000,
                forall |pos: int| 0 <= pos < fi as int ==> #[trigger] freq@[pos] == 0,
            decreases 100_000 - fi,
        {
            freq.push(0);
            fi = fi + 1;
        }

        let mut block_sum: Vec<i64> = Vec::new();
        let mut bi: usize = 0;
        while bi < num_blocks
            invariant
                block_sum@.len() == bi as int,
                0 <= bi <= num_blocks,
                num_blocks == 313,
                forall |bb: int| 0 <= bb < bi as int ==> #[trigger] block_sum@[bb] == 0,
            decreases num_blocks - bi,
        {
            block_sum.push(0);
            bi = bi + 1;
        }
        proof {
            assert forall |pos: int| 0 <= pos < 100_000 implies
                (#[trigger] freq@[pos]) as int == count_in_range(instructions@, 0, pos + 1, pos + 1) by {}
            assert forall |bb: int| 0 <= bb < num_blocks as int implies
                (#[trigger] block_sum@[bb]) as int
                    == count_in_range(instructions@, 0, bb * block_size as int + 1, min_spec((bb + 1) * block_size as int, 100_000)) by {}
            assert forall |pos: int| 0 <= pos < 100_000 implies 0 <= #[trigger] freq@[pos] <= 100_000 by {}
            assert forall |bb: int| 0 <= bb < num_blocks as int implies 0 <= #[trigger] block_sum@[bb] <= 100_000 by {}
        }

        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == instructions.len(),
                1 <= n <= 100_000,
                block_size == 320,
                num_blocks == 313,
                freq@.len() == 100_000,
                block_sum@.len() == num_blocks as int,
                forall |k: int| 0 <= k < n as int ==> 1 <= #[trigger] instructions@[k] <= 100_000,
                forall |pos: int| 0 <= pos < 100_000 ==>
                    (#[trigger] freq@[pos]) as int == count_in_range(instructions@, i as int, pos + 1, pos + 1),
                forall |bb: int| 0 <= bb < num_blocks as int ==>
                    (#[trigger] block_sum@[bb]) as int
                        == count_in_range(instructions@, i as int, bb * block_size as int + 1, min_spec((bb + 1) * block_size as int, 100_000)),
                forall |pos: int| 0 <= pos < 100_000 ==> 0 <= #[trigger] freq@[pos] <= 100_000,
                forall |bb: int| 0 <= bb < num_blocks as int ==> 0 <= #[trigger] block_sum@[bb] <= 100_000,
                cost as int == total_cost(instructions@, i as int),
                0 <= cost <= i as int * i as int,
            decreases n - i
        {
            let val = instructions[i] as usize;
            let b0 = val / block_size;

            proof {
                assert(b0 as int * block_size as int <= val as int) by (nonlinear_arith)
                    requires block_size == 320, b0 == val / block_size, val <= 100_000;
                assert(b0 < num_blocks) by (nonlinear_arith)
                    requires block_size == 320, num_blocks == 313, b0 == val / block_size, val <= 100_000;
            }

            let mut sum: i64 = 0;
            let mut bb: usize = 0;
            while bb < b0
                invariant
                    0 <= bb <= b0,
                    b0 < num_blocks,
                    num_blocks == 313,
                    block_size == 320,
                    i < n,
                    n <= 100_000,
                    n == instructions.len(),
                    block_sum@.len() == num_blocks as int,
                    forall |bbb: int| 0 <= bbb < num_blocks as int ==>
                        (#[trigger] block_sum@[bbb]) as int
                            == count_in_range(instructions@, i as int, bbb * block_size as int + 1, min_spec((bbb + 1) * block_size as int, 100_000)),
                    forall |bbb: int| 0 <= bbb < num_blocks as int ==> 0 <= #[trigger] block_sum@[bbb] <= 100_000,
                    sum as int == blocks_sum_upto(instructions@, i as int, block_size as int, bb as int),
                    0 <= sum <= 100_000,
                decreases b0 - bb,
            {
                proof {
                    let step1 = blocks_sum_upto(instructions@, i as int, block_size as int, bb as int + 1);
                    assert(step1
                        == blocks_sum_upto(instructions@, i as int, block_size as int, bb as int)
                            + count_in_range(instructions@, i as int, bb as int * block_size as int + 1, min_spec((bb as int + 1) * block_size as int, 100_000)));
                    assert(step1 == sum as int + block_sum@[bb as int] as int);
                    blocks_sum_upto_bound(instructions@, i as int, block_size as int, bb as int + 1);
                    assert(step1 <= i as int);
                    assert(sum as int + block_sum@[bb as int] as int <= i as int);
                    assert(i as int <= 100_000);
                    assert((sum as int) + (block_sum@[bb as int] as int) <= 100_000);
                }
                sum = sum + block_sum[bb];
                bb = bb + 1;
            }
            proof {
                blocks_sum_upto_eq(instructions@, i as int, block_size as int, b0 as int);
                assert(min_spec(b0 as int * block_size as int, 100_000) == b0 as int * block_size as int);
            }

            let mut p: usize = b0 * block_size;
            while p < val
                invariant
                    b0 * block_size <= p,
                    p <= val,
                    val <= 100_000,
                    i < n,
                    n <= 100_000,
                    n == instructions.len(),
                    freq@.len() == 100_000,
                    forall |pos: int| 0 <= pos < 100_000 ==>
                        (#[trigger] freq@[pos]) as int == count_in_range(instructions@, i as int, pos + 1, pos + 1),
                    forall |pos: int| 0 <= pos < 100_000 ==> 0 <= #[trigger] freq@[pos] <= 100_000,
                    sum as int == count_in_range(instructions@, i as int, 1, p as int),
                    0 <= sum <= 100_000,
                decreases val - p,
            {
                proof {
                    count_in_range_split(instructions@, i as int, 1, p as int, p as int + 1);
                    let step2 = count_in_range(instructions@, i as int, 1, p as int + 1);
                    assert(step2 == sum as int + freq@[p as int] as int);
                    count_in_range_nonneg(instructions@, i as int, 1, p as int + 1);
                    assert(step2 <= i as int);
                    assert(sum as int + freq@[p as int] as int <= i as int);
                    assert(i as int <= 100_000);
                    assert((sum as int) + (freq@[p as int] as int) <= 100_000);
                }
                sum = sum + freq[p];
                p = p + 1;
            }
            let leq = sum;

            proof {
                count_in_range_split(instructions@, i as int, 1, val as int - 1, val as int);
                count_in_range_nonneg(instructions@, i as int, 1, val as int - 1);
                count_in_range_nonneg(instructions@, i as int, val as int, val as int);
                assert(freq@[val as int - 1] as int == count_in_range(instructions@, i as int, val as int, val as int));
                assert(freq[val - 1] as int <= leq as int);
            }
            let less = leq - freq[val - 1];

            proof {
                count_in_range_split(instructions@, i as int, 1, val as int, 100_000);
                assert forall |k: int| 0 <= k < i as int implies 1 <= #[trigger] instructions@[k] <= 100_000 by {};
                count_in_range_all(instructions@, i as int);
                count_in_range_nonneg(instructions@, i as int, val as int + 1, 100_000);
                assert(leq as int <= i as int);
            }
            let greater = (i as i64) - leq;

            let min_cost: i64 = if less < greater { less } else { greater };
            proof {
                count_less_eq_range(instructions@, i as int, instructions@[i as int]);
                count_greater_eq_range(instructions@, i as int, instructions@[i as int]);
                count_less_bounds(instructions@, i as int, instructions@[i as int]);
                count_greater_bounds(instructions@, i as int, instructions@[i as int]);
                total_cost_bound(instructions@, i as int + 1);
                assert((i as int + 1) * (i as int + 1) <= 100_000 * 100_000) by(nonlinear_arith)
                    requires i as int + 1 <= 100_000;
            }
            cost = cost + min_cost;

            let pos = val - 1;
            proof {
                count_in_range_nonneg(instructions@, i as int, pos as int + 1, pos as int + 1);
                assert(freq@[pos as int] as int <= i as int);
            }
            let ghost freq_before = freq@;
            let ghost block_sum_before = block_sum@;
            freq.set(pos, freq[pos] + 1);
            proof {
                assert(freq@ =~= freq_before.update(pos as int, (freq_before[pos as int] + 1) as i64));
                assert forall |q: int| 0 <= q < 100_000 implies
                    (#[trigger] freq@[q]) as int == count_in_range(instructions@, i as int + 1, q + 1, q + 1) by {
                    count_in_range_step(instructions@, i as int, q + 1, q + 1);
                    if q == pos as int {
                        assert(instructions@[i as int] as int == q + 1);
                    } else {
                        assert(instructions@[i as int] as int != q + 1);
                    }
                }
                assert(i < n && n <= 100_000);
                assert forall |q: int| 0 <= q < 100_000 implies 0 <= #[trigger] freq@[q] <= 100_000 by {}
            }
            let block_idx = pos / block_size;
            proof {
                assert(block_idx as int == pos as int / block_size as int);
                count_in_range_nonneg(instructions@, i as int, block_idx as int * block_size as int + 1, min_spec((block_idx as int + 1) * block_size as int, 100_000));
                assert(block_sum@[block_idx as int] as int <= i as int);
            }
            block_sum.set(block_idx, block_sum[block_idx] + 1);
            proof {
                assert(block_sum@ =~= block_sum_before.update(block_idx as int, (block_sum_before[block_idx as int] + 1) as i64));
                assert forall |bbb: int| 0 <= bbb < num_blocks as int implies
                    (#[trigger] block_sum@[bbb]) as int
                        == count_in_range(instructions@, i as int + 1, bbb * block_size as int + 1, min_spec((bbb + 1) * block_size as int, 100_000)) by {
                    count_in_range_step(instructions@, i as int, bbb * block_size as int + 1, min_spec((bbb + 1) * block_size as int, 100_000));
                    if bbb == block_idx as int {
                        assert(bbb * block_size as int + 1 <= instructions@[i as int] as int
                            && instructions@[i as int] as int <= min_spec((bbb + 1) * block_size as int, 100_000));
                    } else {
                        block_membership_excl(pos as int, block_size as int, bbb);
                        assert(min_spec((bbb + 1) * block_size as int, 100_000) <= (bbb + 1) * block_size as int);
                        assert(!(bbb * block_size as int + 1 <= instructions@[i as int] as int
                            && instructions@[i as int] as int <= min_spec((bbb + 1) * block_size as int, 100_000)));
                    }
                }
                assert(i < n && n <= 100_000);
                assert forall |bbb: int| 0 <= bbb < num_blocks as int implies 0 <= #[trigger] block_sum@[bbb] <= 100_000 by {}
            }

            i = i + 1;
        }
        proof {
            total_cost_nonneg(instructions@, n as int);
        }
        (cost % 1_000_000_007) as i32
    }
}

}
