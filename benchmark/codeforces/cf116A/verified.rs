use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn prefix_sum_entries(entries: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        prefix_sum_entries(entries, end - 1) + entries[end - 1] as int
    }
}

pub open spec fn prefix_sum_exits(exits: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        prefix_sum_exits(exits, end - 1) + exits[end - 1] as int
    }
}

pub open spec fn prefix_passengers(entries: Seq<i32>, exits: Seq<i32>, end: int) -> int {
    prefix_sum_entries(entries, end) - prefix_sum_exits(exits, end)
}

pub open spec fn max_prefix_passengers(entries: Seq<i32>, exits: Seq<i32>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        let prev = max_prefix_passengers(entries, exits, n - 1);
        let curr = prefix_passengers(entries, exits, n);
        if curr > prev {
            curr
        } else {
            prev
        }
    }
}

proof fn lemma_passengers_step(entries: Seq<i32>, exits: Seq<i32>, k: int)
    requires
        0 <= k < entries.len(),
        0 <= k < exits.len(),
    ensures
        prefix_passengers(entries, exits, k + 1) ==
            prefix_passengers(entries, exits, k) - exits[k] as int + entries[k] as int,
{}

proof fn lemma_prefix_sum_entries_upper(entries: Seq<i32>, k: int)
    requires
        0 <= k <= entries.len(),
        forall|i: int| 0 <= i < entries.len() ==> 0 <= #[trigger] entries[i] <= 1000,
    ensures
        prefix_sum_entries(entries, k) <= 1000 * k,
    decreases k,
{
    if k > 0 {
        lemma_prefix_sum_entries_upper(entries, k - 1);
    }
}

proof fn lemma_prefix_sum_exits_nonneg(exits: Seq<i32>, k: int)
    requires
        0 <= k <= exits.len(),
        forall|i: int| 0 <= i < exits.len() ==> 0 <= #[trigger] exits[i],
    ensures
        prefix_sum_exits(exits, k) >= 0,
    decreases k,
{
    if k > 0 {
        lemma_prefix_sum_exits_nonneg(exits, k - 1);
    }
}

proof fn lemma_max_ge_all(entries: Seq<i32>, exits: Seq<i32>, n: int, j: int)
    requires
        0 <= j <= n,
    ensures
        prefix_passengers(entries, exits, j) <= max_prefix_passengers(entries, exits, n),
    decreases n,
{
    if n > 0 && j < n {
        lemma_max_ge_all(entries, exits, n - 1, j);
    }
}

proof fn lemma_max_exists(entries: Seq<i32>, exits: Seq<i32>, n: int)
    requires
        0 <= n,
    ensures
        exists|i: int| 0 <= i <= n
            && prefix_passengers(entries, exits, i) == max_prefix_passengers(entries, exits, n),
    decreases n,
{
    if n > 0 {
        if prefix_passengers(entries, exits, n) > max_prefix_passengers(entries, exits, n - 1) {
            assert(prefix_passengers(entries, exits, n)
                == max_prefix_passengers(entries, exits, n));
        } else {
            lemma_max_exists(entries, exits, n - 1);
            let w = choose|i: int| 0 <= i <= n - 1
                && prefix_passengers(entries, exits, i)
                    == max_prefix_passengers(entries, exits, n - 1);
            assert(0 <= w <= n);
            assert(prefix_passengers(entries, exits, w)
                == max_prefix_passengers(entries, exits, n));
        }
    } else {
        assert(prefix_passengers(entries, exits, 0)
            == max_prefix_passengers(entries, exits, 0));
    }
}

impl Solution {
    pub fn max_passengers(exits: Vec<i32>, entries: Vec<i32>) -> (result: i32)
        requires
            2 <= exits.len() <= 1000,
            exits.len() == entries.len(),
            forall|i: int| 0 <= i < exits.len() ==> 0 <= #[trigger] exits[i] <= 1000,
            forall|i: int| 0 <= i < entries.len() ==> 0 <= #[trigger] entries[i] <= 1000,
            exits[0] == 0,
            entries[exits.len() - 1] == 0,
            forall|i: int| 0 <= i < exits.len() ==>
                #[trigger] exits@[i] as int <= prefix_passengers(entries@, exits@, i),
        ensures
            result as int == max_prefix_passengers(entries@, exits@, exits.len() as int),
            forall|i: int| 0 <= i <= exits.len() as int ==>
                prefix_passengers(entries@, exits@, i) <= result as int,
            exists|i: int| 0 <= i <= exits.len() as int
                && prefix_passengers(entries@, exits@, i) == result as int,
    {
        let n = exits.len();
        let mut max_val = 0i32;
        let mut current = 0i32;
        let mut i = 0usize;
        while i < n
            invariant
                0 <= i <= n,
                n == exits.len(),
                n == entries.len(),
                2 <= n <= 1000,
                current as int == prefix_passengers(entries@, exits@, i as int),
                0 <= current,
                max_val as int == max_prefix_passengers(entries@, exits@, i as int),
                0 <= max_val,
                forall|j: int| 0 <= j < exits.len() ==> 0 <= #[trigger] exits[j] <= 1000,
                forall|j: int| 0 <= j < entries.len() ==> 0 <= #[trigger] entries[j] <= 1000,
                forall|j: int| 0 <= j < exits.len() ==>
                    #[trigger] exits@[j] as int <= prefix_passengers(entries@, exits@, j),
            decreases n - i,
        {
            proof {
                lemma_passengers_step(entries@, exits@, i as int);
                assert(exits[i as int] as int <= current as int);
                lemma_prefix_sum_entries_upper(entries@, (i + 1) as int);
                lemma_prefix_sum_exits_nonneg(exits@, (i + 1) as int);
                assert(prefix_passengers(entries@, exits@, (i + 1) as int) <= 1_000_000) by (nonlinear_arith)
                    requires
                        prefix_sum_entries(entries@, (i + 1) as int) <= 1000 * ((i + 1) as int),
                        prefix_sum_exits(exits@, (i + 1) as int) >= 0,
                        prefix_passengers(entries@, exits@, (i + 1) as int) ==
                            prefix_sum_entries(entries@, (i + 1) as int)
                            - prefix_sum_exits(exits@, (i + 1) as int),
                        (i as int) + 1 <= 1000;
            }
            current = current - exits[i] + entries[i];
            if current > max_val {
                max_val = current;
            }
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j <= exits.len() as int implies
                prefix_passengers(entries@, exits@, j) <= max_val as int by {
                lemma_max_ge_all(entries@, exits@, n as int, j);
            }
            lemma_max_exists(entries@, exits@, n as int);
        }
        max_val
    }
}

}
