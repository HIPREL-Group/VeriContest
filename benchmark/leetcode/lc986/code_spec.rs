use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn interval_rows(list: Seq<Vec<i32>>) -> bool {
        forall |i: int| 0 <= i < list.len() ==> #[trigger] list[i].len() == 2
    }

    pub open spec fn valid_interval(list: Seq<Vec<i32>>, i: int) -> bool {
        0 <= list[i][0] < list[i][1] <= 1_000_000_000
    }

    pub open spec fn disjoint_at(list: Seq<Vec<i32>>, i: int) -> bool {
        list[i][1] < list[i + 1][0]
    }

    pub open spec fn sorted_disjoint(list: Seq<Vec<i32>>) -> bool {
        (forall |i: int| 0 <= i < list.len() ==> Self::valid_interval(list, i))
        && (forall |i: int| 0 <= i < list.len() as int - 1 ==>
            #[trigger] Self::disjoint_at(list, i))
    }

    pub open spec fn max_int(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn min_int(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn intersection_list(
        first: Seq<Vec<i32>>,
        second: Seq<Vec<i32>>,
        i: int,
        j: int,
    ) -> Seq<Seq<i32>>
        decreases
            (first.len() - i) + (second.len() - j),
    {
        if i >= first.len() as int || j >= second.len() as int {
            Seq::empty()
        } else {
            let a0 = first[i][0] as int;
            let a1 = first[i][1] as int;
            let b0 = second[j][0] as int;
            let b1 = second[j][1] as int;
            let lo = Self::max_int(a0, b0);
            let hi = Self::min_int(a1, b1);
            let (i2, j2) = if a1 < b1 { (i + 1, j) } else { (i, j + 1) };
            let rest = Self::intersection_list(first, second, i2, j2);
            if lo <= hi {
                let interval = Seq::new(2, |k: int| if k == 0 { lo as i32 } else { hi as i32 });
                let one = Seq::new(1, |k: int| interval);
                one.add(rest)
            } else {
                rest
            }
        }
    }

    pub fn interval_intersection(
        first_list: Vec<Vec<i32>>,
        second_list: Vec<Vec<i32>>,
    ) -> (result: Vec<Vec<i32>>)
        requires
            0 <= first_list.len() <= 1000,
            0 <= second_list.len() <= 1000,
            first_list.len() + second_list.len() >= 1,
            Self::interval_rows(first_list@),
            Self::interval_rows(second_list@),
            Self::sorted_disjoint(first_list@),
            Self::sorted_disjoint(second_list@),
        ensures
            forall |k: int| 0 <= k < result@.len() ==>
                result@[k].len() == 2 && result@[k][0] <= result@[k][1],
            forall |k: int| 0 <= k < result@.len() as int - 1 ==>
                #[trigger] result@[k][0] <= result@[k + 1][0],
            result@.len() == Self::intersection_list(first_list@, second_list@, 0, 0).len(),
            forall |k: int| 0 <= k < result@.len() ==>
                result@[k][0] == Self::intersection_list(first_list@, second_list@, 0, 0)[k][0]
                && result@[k][1] == Self::intersection_list(first_list@, second_list@, 0, 0)[k][1],
    {
        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut i = 0usize;
        let mut j = 0usize;
        let n = first_list.len();
        let m = second_list.len();
        while i < n && j < m {
            let lo = first_list[i][0].max(second_list[j][0]);
            let hi = first_list[i][1].min(second_list[j][1]);
            if lo <= hi {
                result.push(vec![lo, hi]);
            }
            if first_list[i][1] < second_list[j][1] {
                i += 1;
            } else {
                j += 1;
            }
        }
        result
    }
}

}
