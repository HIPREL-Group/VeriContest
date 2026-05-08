use vstd::prelude::*;

verus! {

pub open spec fn spec_count_tested(bp: Seq<i32>, k: int, tested: int) -> int
    decreases bp.len() - k,
{
    if k >= bp.len() {
        tested
    } else if bp[k] > tested {
        spec_count_tested(bp, k + 1, tested + 1)
    } else {
        spec_count_tested(bp, k + 1, tested)
    }
}

pub open spec fn spec_count_tested_devices(bp: Seq<i32>) -> int
{
    spec_count_tested(bp, 0, 0)
}

proof fn lemma_count_tested_bounds(bp: Seq<i32>, k: int, tested: int)
    requires
        0 <= k <= bp.len(),
        bp.len() <= 100,
        0 <= tested <= 100,
        forall|j: int| 0 <= j < bp.len() ==> 0 <= #[trigger] bp[j] <= 100,
    ensures
        tested <= spec_count_tested(bp, k, tested) <= tested + (bp.len() - k),
    decreases bp.len() - k,
{
    if k >= bp.len() {
    } else if bp[k] > tested {
        lemma_count_tested_bounds(bp, k + 1, tested + 1);
    } else {
        lemma_count_tested_bounds(bp, k + 1, tested);
    }
}

fn count_tested_devices(battery_percentages: Vec<i32>) -> (result: i32)
    requires
        1 <= battery_percentages.len() <= 100,
        forall|i: int| 0 <= i < battery_percentages.len() ==> 0 <= #[trigger] battery_percentages[i] <= 100,
    ensures
        result as int == spec_count_tested_devices(battery_percentages@),
{
    let n = battery_percentages.len();
    let mut tested = 0i32;
    let mut i = 0;

    proof {
        lemma_count_tested_bounds(battery_percentages@, 0, 0);
    }

    while i < n
        invariant
            0 <= i <= n,
            n == battery_percentages.len(),
            1 <= n <= 100,
            forall|j: int| 0 <= j < battery_percentages.len() ==> 0 <= #[trigger] battery_percentages@[j] <= 100,
            0 <= tested <= 100,
            spec_count_tested(battery_percentages@, i as int, tested as int) == spec_count_tested_devices(battery_percentages@),
        decreases n - i,
    {
        proof {
            lemma_count_tested_bounds(battery_percentages@, (i + 1) as int, if battery_percentages@[i as int] > tested as int { tested as int + 1 } else { tested as int });
        }

        if battery_percentages[i] > tested {
            tested = tested + 1;
        }
        i = i + 1;
    }
    tested
}

}

fn main() {}
