use vstd::prelude::*;

verus! {

pub open spec fn spec_prev(i: int, n: int) -> int
{
    if i == 0 { n - 1 } else { i - 1 }
}

pub open spec fn spec_next(i: int, n: int) -> int
{
    if i == n - 1 { 0 } else { i + 1 }
}

pub open spec fn spec_is_alternating(colors: Seq<i32>, i: int) -> bool
{
    let n = colors.len() as int;
    colors[i] != colors[spec_prev(i, n)] && colors[i] != colors[spec_next(i, n)]
}

pub open spec fn spec_count_alternating(colors: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        spec_count_alternating(colors, k - 1) + if spec_is_alternating(colors, k - 1) {
            1 as int
        } else {
            0 as int
        }
    }
}

pub open spec fn spec_number_of_alternating_groups(colors: Seq<i32>) -> int
{
    spec_count_alternating(colors, colors.len() as int)
}

fn number_of_alternating_groups(colors: Vec<i32>) -> (result: i32)
    requires
        3 <= colors.len() <= 100,
        forall|i: int| 0 <= i < colors.len() ==> 0 <= #[trigger] colors[i] <= 1,
    ensures
        result as int == spec_number_of_alternating_groups(colors@),
{
    let n = colors.len();
    let mut count = 0i32;
    let mut i = 0;
    while i < n
        decreases n - i,
    {
        let prev = (i + n - 1) % n;
        let next = (i + 1) % n;
        if colors[i] != colors[prev] && colors[i] != colors[next] {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}

}
