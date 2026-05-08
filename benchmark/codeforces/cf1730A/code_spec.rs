use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_prefix_count(a: Seq<i32>, i: int, v: int) -> int
    decreases i,
{
    if i <= 0 {
        0int
    } else {
        spec_prefix_count(a, i - 1, v) + if a[i - 1] as int == v { 1int } else { 0int }
    }
}

pub open spec fn spec_orbit_contrib(k: int, c: int) -> int {
    if k <= 0 {
        0int
    } else if k < c {
        k
    } else {
        c
    }
}

pub open spec fn spec_sum_min_cost(a: Seq<i32>, c: int, vmax: int) -> int
    decreases vmax,
{
    if vmax <= 0 {
        0int
    } else {
        let k = spec_prefix_count(a, a.len() as int, vmax);
        spec_orbit_contrib(k, c) + spec_sum_min_cost(a, c, vmax - 1)
    }
}

impl Solution {
    pub fn min_destroy_cost(orbits: Vec<i32>, c: i32) -> (res: i32)
        requires
            1 <= orbits.len() <= 100,
            1 <= c <= 100,
            forall|i: int| 0 <= i < orbits.len() ==> 1 <= #[trigger] orbits@[i] <= 100,
        ensures
            res as int == spec_sum_min_cost(orbits@, c as int, 100),
    {
        let n = orbits.len();
        let mut cnt: Vec<i32> = Vec::new();
        let mut t = 0usize;
        while t < 101 {
            cnt.push(0);
            t = t + 1;
        }
        let mut i = 0usize;
        while i < n {
            let x = orbits[i] as usize;
            let prev = cnt[x];
            cnt.set(x, prev + 1);
            i = i + 1;
        }
        let mut ans = 0i32;
        let mut v = 1usize;
        while v <= 100 {
            let k = cnt[v];
            let add = if k < c {
                k
            } else {
                c
            };
            ans = ans + add;
            v = v + 1;
        }
        ans
    }
}

}
