use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count(s: Seq<i32>, v: i32) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            (if s.last() == v { 1int } else { 0int }) + Self::count(s.drop_last(), v)
        }
    }

    proof fn count_nonneg(s: Seq<i32>, v: i32)
        ensures
            Self::count(s, v) >= 0,
        decreases s.len(),
    {
        if s.len() > 0 {
            Self::count_nonneg(s.drop_last(), v);
        }
    }

    proof fn count_take_step(s: Seq<i32>, v: i32, n: int)
        requires
            0 <= n < s.len() as int,
        ensures
            Self::count(s.take(n + 1), v)
                == Self::count(s.take(n), v)
                    + (if s[n] == v { 1int } else { 0int }),
    {
        assert(s.take(n + 1).drop_last() =~= s.take(n));
    }

    proof fn count_zero_for_absent(s: Seq<i32>, v: i32)
        requires
            forall|i: int| 0 <= i < s.len() ==> s[i] != v,
        ensures
            Self::count(s, v) == 0,
        decreases s.len(),
    {
        if s.len() > 0 {
            Self::count_zero_for_absent(s.drop_last(), v);
        }
    }

    proof fn count_upper_bound(s: Seq<i32>, v: i32)
        ensures
            Self::count(s, v) <= s.len(),
        decreases s.len(),
    {
        if s.len() > 0 {
            Self::count_upper_bound(s.drop_last(), v);
        }
    }

    pub fn can_be_equal(target: Vec<i32>, arr: Vec<i32>) -> (res: bool)
        requires
            target.len() == arr.len(),
            1 <= target.len() <= 1000,
            forall |i: int| 0 <= i < target.len() ==> 1 <= #[trigger] target[i] <= 1000,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1000,
        ensures
            res == (forall |v: i32| Self::count(target@, v) == Self::count(arr@, v)),
    {
        let n = target.len();
        let mut counts: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < 1001
            invariant
                0 <= k <= 1001,
                counts.len() == k,
                forall |j: int| 0 <= j < k ==> counts[j] == 0i32,
            decreases 1001 - k,
        {
            counts.push(0i32);
            k = k + 1;
        }
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == target.len(),
                n == arr.len(),
                n <= 1000,
                counts.len() == 1001,
                forall |j: int| 0 <= j < target.len() ==> 1 <= #[trigger] target[j] <= 1000,
                forall |j: int| 0 <= j < arr.len() ==> 1 <= #[trigger] arr[j] <= 1000,
                forall |v: int| 0 <= v <= 1000 ==>
                    counts[v] == Self::count(target@.take(i as int), v as i32)
                        - Self::count(arr@.take(i as int), v as i32),
            decreases n - i,
        {
            let tv = target[i];
            let av = arr[i];

            proof {
                Self::count_nonneg(target@.take(i as int), tv);
                Self::count_upper_bound(target@.take(i as int), tv);
                Self::count_nonneg(arr@.take(i as int), tv);
                Self::count_upper_bound(arr@.take(i as int), tv);
                Self::count_nonneg(target@.take(i as int), av);
                Self::count_upper_bound(target@.take(i as int), av);
                Self::count_nonneg(arr@.take(i as int), av);
                Self::count_upper_bound(arr@.take(i as int), av);

                assert forall |v: int| 0 <= v <= 1000 implies
                    (#[trigger] Self::count(target@.take(i as int + 1), v as i32))
                        == Self::count(target@.take(i as int), v as i32)
                            + (if target@[i as int] == v as i32 { 1int } else { 0int })
                by {
                    Self::count_take_step(target@, v as i32, i as int);
                };
                assert forall |v: int| 0 <= v <= 1000 implies
                    (#[trigger] Self::count(arr@.take(i as int + 1), v as i32))
                        == Self::count(arr@.take(i as int), v as i32)
                            + (if arr@[i as int] == v as i32 { 1int } else { 0int })
                by {
                    Self::count_take_step(arr@, v as i32, i as int);
                };
            }

            counts.set(tv as usize, counts[tv as usize] + 1);
            counts.set(av as usize, counts[av as usize] - 1);
            i = i + 1;
        }

        assert(target@.take(n as int) =~= target@);
        assert(arr@.take(n as int) =~= arr@);

        let mut k2: usize = 0;
        while k2 < 1001
            invariant
                0 <= k2 <= 1001,
                counts.len() == 1001,
                forall |v: int| 0 <= v <= 1000 ==>
                    counts[v] == Self::count(target@, v as i32)
                        - Self::count(arr@, v as i32),
                forall |v: int| 0 <= v < k2 ==> counts[v] == 0i32,
            decreases 1001 - k2,
        {
            if counts[k2] != 0 {
                return false;
            }
            k2 = k2 + 1;
        }

        proof {
            assert forall |v: i32| Self::count(target@, v) == Self::count(arr@, v) by {
                if 0 <= v <= 1000 {
                    assert(counts[v as int] == 0i32);
                } else {
                    Self::count_zero_for_absent(target@, v);
                    Self::count_zero_for_absent(arr@, v);
                }
            };
        }

        true
    }
}

}
