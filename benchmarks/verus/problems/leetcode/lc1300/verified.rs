use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn min_spec(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn mutated_sum(arr: Seq<i32>, value: int) -> int
    decreases arr.len()
{
    if arr.len() == 0 {
        0
    } else {
        min_spec(arr[arr.len() - 1] as int, value) + mutated_sum(arr.drop_last(), value)
    }
}

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

proof fn mutated_sum_monotone(arr: Seq<i32>, v1: int, v2: int)
    requires v1 <= v2
    ensures mutated_sum(arr, v1) <= mutated_sum(arr, v2)
    decreases arr.len()
{
    if arr.len() > 0 {
        mutated_sum_monotone(arr.drop_last(), v1, v2);
    }
}

proof fn mutated_sum_at_zero(arr: Seq<i32>)
    requires forall |i: int| 0 <= i < arr.len() ==> arr[i] >= 1
    ensures mutated_sum(arr, 0) == 0
    decreases arr.len()
{
    if arr.len() > 0 {
        mutated_sum_at_zero(arr.drop_last());
    }
}

proof fn mutated_sum_constant_above_max(arr: Seq<i32>, v1: int, v2: int)
    requires
        v1 <= v2,
        forall |i: int| 0 <= i < arr.len() ==> arr[i] as int <= v1,
    ensures
        mutated_sum(arr, v1) == mutated_sum(arr, v2)
    decreases arr.len()
{
    if arr.len() > 0 {
        mutated_sum_constant_above_max(arr.drop_last(), v1, v2);
    }
}

proof fn mutated_sum_strict_monotone(arr: Seq<i32>, v: int)
    requires
        arr.len() > 0,
        forall |i: int| 0 <= i < arr.len() ==> arr[i] as int >= 1,
        exists |i: int| 0 <= i < arr.len() && arr[i] as int > v,
        v >= 0,
    ensures
        mutated_sum(arr, v) < mutated_sum(arr, v + 1)
    decreases arr.len()
{
    let last = (arr.len() - 1) as int;
    if arr[last] as int > v {
        mutated_sum_monotone(arr.drop_last(), v, v + 1);
    } else {
        let witness = choose |i: int| 0 <= i < arr.len() && arr[i] as int > v;
        assert(witness != last);
        assert(arr.drop_last()[witness] == arr[witness]);
        mutated_sum_strict_monotone(arr.drop_last(), v);
    }
}

fn compute_sum(arr: &Vec<i32>, value: i32) -> (result: i32)
    requires
        1 <= arr.len() <= 10_000,
        forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100_000,
        0 <= value <= 100_000,
    ensures
        result as int == mutated_sum(arr@, value as int),
{
    let n = arr.len();
    let mut sum: i32 = 0;
    let mut j: usize = 0;
    while j < n
        invariant
            0 <= j <= n,
            n == arr.len(),
            n <= 10_000,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100_000,
            0 <= value <= 100_000,
            sum as int == mutated_sum(arr@.subrange(0, j as int), value as int),
            0 <= sum <= j as int * 100_000,
        decreases n - j,
    {
        proof {
            let s = arr@.subrange(0, (j + 1) as int);
            assert(s.len() == j + 1);
            assert(s[s.len() - 1] == arr@[j as int]);
            assert(s.drop_last() =~= arr@.subrange(0, j as int));
        }
        if arr[j] <= value {
            sum = sum + arr[j];
        } else {
            sum = sum + value;
        }
        j = j + 1;
    }
    proof {
        assert(arr@.subrange(0, n as int) =~= arr@);
    }
    sum
}

impl Solution {
    pub fn find_best_value(arr: Vec<i32>, target: i32) -> (result: i32)
        requires
            1 <= arr.len() <= 10_000,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100_000,
            1 <= target <= 100_000,
        ensures
            result >= 0,
            forall |v: int| #![trigger mutated_sum(arr@, v)] v >= 0 ==> abs_diff(mutated_sum(arr@, result as int), target as int) <= abs_diff(mutated_sum(arr@, v), target as int),
            forall |v: int| #![trigger mutated_sum(arr@, v)] (v >= 0 && abs_diff(mutated_sum(arr@, v), target as int) == abs_diff(mutated_sum(arr@, result as int), target as int)) ==> result as int <= v,
    {
        let n = arr.len();
        let mut max_val: i32 = arr[0];
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= n <= 10_000,
                n == arr.len(),
                1 <= i <= n,
                1 <= max_val <= 100_000,
                forall |j: int| 0 <= j < i as int ==> #[trigger] arr[j] <= max_val,
                exists |j: int| 0 <= j < i as int && arr[j] == max_val,
                forall |j: int| 0 <= j < arr.len() ==> 1 <= #[trigger] arr[j] <= 100_000,
            decreases n - i,
        {
            if arr[i] > max_val {
                max_val = arr[i];
            }
            i = i + 1;
        }

        let total_sum = compute_sum(&arr, max_val);

        if total_sum <= target {
            proof {
                assert forall |v: int| #![trigger mutated_sum(arr@, v)] v >= 0 implies abs_diff(mutated_sum(arr@, max_val as int), target as int) <= abs_diff(mutated_sum(arr@, v), target as int) by {
                    if v <= max_val as int {
                        mutated_sum_monotone(arr@, v, max_val as int);
                    } else {
                        mutated_sum_constant_above_max(arr@, max_val as int, v);
                    }
                };
                assert forall |v: int| #![trigger mutated_sum(arr@, v)] (v >= 0 && abs_diff(mutated_sum(arr@, v), target as int) == abs_diff(mutated_sum(arr@, max_val as int), target as int)) implies max_val as int <= v by {
                    if v < max_val as int {
                        let w = choose |j: int| 0 <= j < arr@.len() && arr@[j] == max_val;
                        assert(arr@[w] as int > v);
                        mutated_sum_strict_monotone(arr@, v);
                        if v + 1 < max_val as int {
                            mutated_sum_monotone(arr@, v + 1, max_val as int);
                        }
                    }
                };
            }
            return max_val;
        }

        let mut lo: i32 = 0;
        let mut hi: i32 = max_val;
        while lo < hi
            invariant
                0 <= lo <= hi <= max_val as int,
                lo as int > 0 ==> mutated_sum(arr@, lo as int - 1) < target as int,
                mutated_sum(arr@, hi as int) >= target as int,
                1 <= arr.len() <= 10_000,
                1 <= max_val <= 100_000,
                forall |j: int| 0 <= j < arr.len() ==> 1 <= #[trigger] arr[j] <= 100_000,
                forall |j: int| 0 <= j < arr.len() ==> arr[j] <= max_val,
                exists |j: int| 0 <= j < arr.len() && arr[j] == max_val,
                1 <= target <= 100_000,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            let sum_mid = compute_sum(&arr, mid);
            if sum_mid >= target {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }

        proof {
            mutated_sum_at_zero(arr@);
        }
        assert(lo >= 1);

        let sum_lo = compute_sum(&arr, lo);
        let sum_prev = compute_sum(&arr, lo - 1);

        proof {
            mutated_sum_monotone(arr@, 0, lo as int - 1);
        }

        if sum_lo - target < target - sum_prev {
            proof {
                assert forall |v: int| #![trigger mutated_sum(arr@, v)] v >= 0 implies abs_diff(mutated_sum(arr@, lo as int), target as int) <= abs_diff(mutated_sum(arr@, v), target as int) by {
                    if v >= lo as int {
                        mutated_sum_monotone(arr@, lo as int, v);
                    } else {
                        mutated_sum_monotone(arr@, v, lo as int - 1);
                    }
                };
                assert forall |v: int| #![trigger mutated_sum(arr@, v)] (v >= 0 && abs_diff(mutated_sum(arr@, v), target as int) == abs_diff(mutated_sum(arr@, lo as int), target as int)) implies lo as int <= v by {
                    if v < lo as int {
                        mutated_sum_monotone(arr@, v, lo as int - 1);
                    }
                };
            }
            lo
        } else {
            proof {
                assert forall |v: int| #![trigger mutated_sum(arr@, v)] v >= 0 implies abs_diff(mutated_sum(arr@, lo as int - 1), target as int) <= abs_diff(mutated_sum(arr@, v), target as int) by {
                    if v >= lo as int {
                        mutated_sum_monotone(arr@, lo as int, v);
                    } else {
                        mutated_sum_monotone(arr@, v, lo as int - 1);
                    }
                };
                assert forall |v: int| #![trigger mutated_sum(arr@, v)] (v >= 0 && abs_diff(mutated_sum(arr@, v), target as int) == abs_diff(mutated_sum(arr@, lo as int - 1), target as int)) implies lo as int - 1 <= v by {
                    if v < lo as int - 1 {
                        let w = choose |j: int| 0 <= j < arr@.len() && arr@[j] == max_val;
                        assert(arr@[w] as int > v);
                        mutated_sum_strict_monotone(arr@, v);
                        if v + 1 < lo as int - 1 {
                            mutated_sum_monotone(arr@, v + 1, lo as int - 1);
                        }
                    }
                };
            }
            lo - 1
        }
    }
}

}
