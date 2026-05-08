use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn first_le(prices: Seq<i32>, i: int, j: int) -> int
        decreases prices.len() - j,
    {
        if j >= prices.len() {
            prices.len() as int
        } else if prices[j] <= prices[i] {
            j
        } else {
            Self::first_le(prices, i, j + 1)
        }
    }

    pub open spec fn expected_price(prices: Seq<i32>, i: int) -> int {
        let j = Self::first_le(prices, i, i + 1);
        if j < prices.len() as int {
            prices[i] as int - prices[j] as int
        } else {
            prices[i] as int
        }
    }

    proof fn lemma_first_le_skip(prices: Seq<i32>, idx: int, start: int, end: int)
        requires
            0 <= idx < prices.len(),
            idx < start,
            start <= end <= prices.len(),
            forall|j: int| start <= j < end ==> prices[j] > prices[idx],
        ensures
            Self::first_le(prices, idx, start) == Self::first_le(prices, idx, end),
        decreases end - start,
    {
        if start < end {
            Self::lemma_first_le_skip(prices, idx, start + 1, end);
        }
    }

    proof fn lemma_first_le_found(prices: Seq<i32>, idx: int, start: int, target: int)
        requires
            0 <= idx < prices.len(),
            idx < start,
            start <= target < prices.len(),
            prices[target] <= prices[idx],
            forall|j: int| start <= j < target ==> prices[j] > prices[idx],
        ensures
            Self::first_le(prices, idx, start) == target,
    {
        Self::lemma_first_le_skip(prices, idx, start, target);
    }

    proof fn lemma_first_le_none(prices: Seq<i32>, idx: int, start: int)
        requires
            0 <= idx < prices.len(),
            idx < start,
            start <= prices.len(),
            forall|j: int| start <= j < prices.len() ==> prices[j] > prices[idx],
        ensures
            Self::first_le(prices, idx, start) == prices.len() as int,
    {
        Self::lemma_first_le_skip(prices, idx, start, prices.len() as int);
    }

    pub fn final_prices(prices: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= prices.len() <= 500,
            forall|i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] <= 1000,
        ensures
            result.len() == prices.len(),
            forall|i: int|
                0 <= i < result.len() ==> #[trigger] result[i] as int == Self::expected_price(
                    prices@,
                    i,
                ),
    {
        let n = prices.len();
        let mut answer: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                n == prices.len(),
                0 <= idx <= n,
                answer.len() == idx,
                forall|k: int| 0 <= k < idx as int ==> answer[k] == prices[k as int],
            decreases n - idx,
        {
            answer.push(prices[idx]);
            idx += 1;
        }
        let ghost mut done: Seq<bool> = Seq::new(n as nat, |_k: int| false);
        let mut stack: Vec<usize> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                n == prices.len(),
                n == answer.len(),
                0 <= i <= n,
                done.len() == n as nat,
                forall|k: int| 0 <= k < n as int ==> 1 <= #[trigger] prices[k] <= 1000,
                
                forall|k: int| 0 <= k < stack.len() ==> 0 <= #[trigger] stack[k] < i,
                
                forall|a: int, b: int| 0 <= a < b < stack.len()
                    ==> #[trigger] stack[a] < #[trigger] stack[b],
                
                forall|a: int, b: int| 0 <= a < b < stack.len()
                    ==> prices[#[trigger] stack[a] as int] < prices[#[trigger] stack[b] as int],
                
                forall|s: int, j: int|
                    #![trigger stack[s], prices[j]]
                    0 <= s < stack.len() && stack[s] as int + 1 <= j < i as int
                    ==> prices[j] > prices[stack[s] as int],
                
                forall|k: int| 0 <= k < n as int && #[trigger] done[k]
                    ==> answer[k] as int == Self::expected_price(prices@, k),
                
                forall|k: int| 0 <= k < n as int && !#[trigger] done[k]
                    ==> answer[k] == prices[k],
                
                forall|s: int| 0 <= s < stack.len() ==> !done[#[trigger] stack[s] as int],
                
                forall|k: int| 0 <= k < i as int ==> (
                    #[trigger] done[k]
                    || (exists|s: int| 0 <= s < stack.len() && stack[s] as int == k)
                ),
                
                forall|k: int| i as int <= k < n as int ==> !#[trigger] done[k],
            decreases n - i,
        {
            while stack.len() > 0 && prices[i] <= prices[stack[stack.len() - 1]]
                invariant
                    n == prices.len(),
                    n == answer.len(),
                    0 <= i < n,
                    done.len() == n as nat,
                    forall|k: int| 0 <= k < n as int ==> 1 <= #[trigger] prices[k] <= 1000,
                    forall|k: int| 0 <= k < stack.len() ==> 0 <= #[trigger] stack[k] < i,
                    forall|a: int, b: int| 0 <= a < b < stack.len()
                        ==> #[trigger] stack[a] < #[trigger] stack[b],
                    forall|a: int, b: int| 0 <= a < b < stack.len()
                        ==> prices[#[trigger] stack[a] as int] < prices[#[trigger] stack[b] as int],
                    forall|s: int, j: int|
                        #![trigger stack[s], prices[j]]
                        0 <= s < stack.len() && stack[s] as int + 1 <= j < i as int
                        ==> prices[j] > prices[stack[s] as int],
                    forall|k: int| 0 <= k < n as int && #[trigger] done[k]
                        ==> answer[k] as int == Self::expected_price(prices@, k),
                    forall|k: int| 0 <= k < n as int && !#[trigger] done[k]
                        ==> answer[k] == prices[k],
                    forall|s: int| 0 <= s < stack.len() ==> !done[#[trigger] stack[s] as int],
                    forall|k: int| 0 <= k < i as int ==> (
                        #[trigger] done[k]
                        || (exists|s: int| 0 <= s < stack.len() && stack[s] as int == k)
                    ),
                    forall|k: int| i as int <= k < n as int ==> !#[trigger] done[k],
                decreases stack.len(),
            {
                let top_idx = stack[stack.len() - 1];
                proof {
                    Self::lemma_first_le_found(
                        prices@, top_idx as int, top_idx as int + 1, i as int,
                    );
                }
                let ghost old_done = done;
                let ghost old_stack_seq = stack@;
                answer.set(top_idx, prices[top_idx] - prices[i]);
                proof {
                    done = done.update(top_idx as int, true);
                }
                stack.pop();
                proof {
                    assert forall|k: int| 0 <= k < i as int implies (
                        #[trigger] done[k]
                        || (exists|s: int| 0 <= s < stack.len() && stack[s] as int == k)
                    ) by {
                        if !done[k] {
                            assert(k != top_idx as int);
                            assert(!old_done[k]);
                            let s0 = choose|s0: int|
                                0 <= s0 < old_stack_seq.len() && old_stack_seq[s0] as int == k;
                            assert(old_stack_seq[old_stack_seq.len() as int - 1] == top_idx);
                            assert(s0 != old_stack_seq.len() as int - 1);
                            assert(0 <= s0 < stack.len());
                            assert(stack@[s0] == old_stack_seq[s0]);
                            assert(stack@[s0] as int == k);
                        }
                    };
                }
            }
            proof {
                assert forall|s: int| 0 <= s < stack.len()
                    implies prices[i as int] > prices[#[trigger] stack[s] as int]
                by {
                    if stack.len() > 0 {
                        let top = (stack.len() - 1) as int;
                        if s < top {
                            assert(prices[stack[s] as int] < prices[stack[top] as int]);
                        }
                    }
                };
            }
            let ghost pre_push_stack = stack@;
            stack.push(i);
            proof {
                assert forall|k: int| 0 <= k < i as int + 1 implies (
                    #[trigger] done[k]
                    || (exists|s: int| 0 <= s < stack.len() && stack[s] as int == k)
                ) by {
                    if k == i as int {
                        assert(stack@[stack.len() as int - 1] == i);
                    } else if !done[k] {
                        let s0 = choose|s0: int|
                            0 <= s0 < pre_push_stack.len()
                                && pre_push_stack[s0] as int == k;
                        assert(stack@[s0] == pre_push_stack[s0]);
                        assert(0 <= s0 < stack.len());
                        assert(stack@[s0] as int == k);
                    }
                };
            }
            i += 1;
        }
        proof {
            assert forall|k: int| 0 <= k < n as int
                implies #[trigger] answer[k] as int == Self::expected_price(prices@, k)
            by {
                if done[k] {
                    
                } else {
                    
                    
                    
                    
                    
                    
                    
                    
                    let s = choose|s: int| 0 <= s < stack.len() && stack[s] as int == k;
                    Self::lemma_first_le_none(prices@, k, k + 1);
                }
            };
        }
        answer
    }
}

}
