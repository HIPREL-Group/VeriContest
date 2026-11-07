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
        let m = requests.len();
        let mut total: u32 = 1;
        let mut p: usize = 0;
        while p < m {
            total = total * 2;
            p += 1;
        }
        let mut net: Vec<i32> = Vec::new();
        let mut init_k: usize = 0;
        while init_k < n as usize {
            net.push(0i32);
            init_k += 1;
        }
        let mut best: i32 = 0;
        let mut mask: u32 = 0;
        while mask < total {
            let mut r: usize = 0;
            while r < n as usize {
                net.set(r, 0i32);
                r += 1;
            }
            let mut count: i32 = 0;
            let mut j: usize = 0;
            let mut pow_j: u32 = 1;
            while j < m {
                if (mask / pow_j) % 2 == 1 {
                    let from_b = requests[j][0] as usize;
                    let to_b = requests[j][1] as usize;
                    let old_from = net[from_b];
                    net.set(from_b, old_from - 1);
                    let cur_to = net[to_b];
                    net.set(to_b, cur_to + 1);
                    count += 1;
                }
                pow_j = pow_j * 2;
                j += 1;
            }
            let mut balanced: bool = true;
            let mut k: usize = 0;
            while k < n as usize {
                if net[k] != 0 {
                    balanced = false;
                }
                k += 1;
            }
            if balanced && count > best {
                best = count;
            }
            mask += 1;
        }
        best
    }
}

}
