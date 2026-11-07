use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn partition_sum(parts: Seq<int>, hi: int) -> int
        decreases hi,
    {
        if hi <= 0 {
            0
        } else {
            Self::partition_sum(parts, hi - 1) + parts[hi - 1]
        }
    }

    pub open spec fn partition_product(parts: Seq<int>, hi: int) -> int
        decreases hi,
    {
        if hi <= 0 {
            1
        } else {
            Self::partition_product(parts, hi - 1) * parts[hi - 1]
        }
    }

    pub fn max_nice_divisors(prime_factors: i32) -> (res: i32)
        requires
            1 <= prime_factors <= 1_000_000_000,
        ensures
            0 <= res,
            exists |parts: Seq<int>|
                #![trigger Self::partition_product(parts, parts.len() as int)]
                parts.len() > 0
                && (forall |i: int| 0 <= i < parts.len() ==> parts[i] >= 1)
                && Self::partition_sum(parts, parts.len() as int) == prime_factors as int
                && Self::partition_product(parts, parts.len() as int) % 1_000_000_007 == res as int
                && (forall |other: Seq<int>|
                    #![trigger Self::partition_product(other, other.len() as int)]
                    other.len() > 0
                    && (forall |j: int| 0 <= j < other.len() ==> other[j] >= 1)
                    && Self::partition_sum(other, other.len() as int) == prime_factors as int
                    ==> Self::partition_product(other, other.len() as int)
                        <= Self::partition_product(parts, parts.len() as int)),
    {
    }
}

} 
