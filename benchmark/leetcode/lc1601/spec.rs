use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn pow2(n: int) -> int
    decreases n,
{
    if n <= 0 { 1 }
    else { 2 * pow2(n - 1) }
}

pub open spec fn bit_set(mask: int, j: int) -> bool {
    (mask / pow2(j)) % 2 == 1
}

pub open spec fn count_ones(mask: int, len: int) -> int
    decreases len,
{
    if len <= 0 { 0 }
    else {
        count_ones(mask, len - 1) + if bit_set(mask, len - 1) { 1int } else { 0int }
    }
}

pub open spec fn net_change_for(requests: Seq<Vec<i32>>, mask: int, building: int, len: int) -> int
    decreases len,
{
    if len <= 0 { 0 }
    else {
        let prev = net_change_for(requests, mask, building, len - 1);
        if bit_set(mask, len - 1) {
            prev
            - (if requests[len - 1][0] as int == building { 1int } else { 0int })
            + (if requests[len - 1][1] as int == building { 1int } else { 0int })
        } else {
            prev
        }
    }
}

pub open spec fn is_balanced(requests: Seq<Vec<i32>>, mask: int, n: int, m: int) -> bool {
    forall|b: int| 0 <= b < n ==> net_change_for(requests, mask, b, m) == 0
}

impl Solution {
    pub fn maximum_requests(n: i32, requests: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= n <= 20,
            1 <= requests.len() <= 16,
            forall|i: int| 0 <= i < requests.len() ==>
                #[trigger] requests[i].len() == 2
                && 0 <= requests[i][0] < n
                && 0 <= requests[i][1] < n,
        ensures
            0 <= result as int <= requests.len(),
            exists|mask: int| 0 <= mask < pow2(requests.len() as int)
                && is_balanced(requests@, mask, n as int, requests.len() as int)
                && result as int == count_ones(mask, requests.len() as int),
            forall|mask: int| (0 <= mask < pow2(requests.len() as int)
                && is_balanced(requests@, mask, n as int, requests.len() as int))
                ==> count_ones(mask, requests.len() as int) <= result as int,
    {
    }
}

}
