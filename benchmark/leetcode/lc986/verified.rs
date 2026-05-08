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

    pub proof fn lemma_intersection_list_sorted(
        first: Seq<Vec<i32>>,
        second: Seq<Vec<i32>>,
        i: int,
        j: int,
    )
        requires
            0 <= i <= first.len(),
            0 <= j <= second.len(),
            Self::sorted_disjoint(first),
            Self::sorted_disjoint(second),
        ensures
            forall |k: int| 0 <= k < Self::intersection_list(first, second, i, j).len() as int - 1 ==>
                #[trigger] Self::intersection_list(first, second, i, j)[k][0]
                    <= Self::intersection_list(first, second, i, j)[k + 1][0],
        decreases
            (first.len() - i) + (second.len() - j),
    {
        if i >= first.len() as int || j >= second.len() as int {
        } else {
            let (i2, j2) = (
                if (first[i][1] as int) < (second[j][1] as int) { i + 1 } else { i },
                if (first[i][1] as int) < (second[j][1] as int) { j } else { j + 1 },
            );
            Self::lemma_intersection_list_sorted(first, second, i2, j2);
            reveal_with_fuel(Solution::intersection_list, 1);
            let rest = Self::intersection_list(first, second, i2, j2);
            let a0 = first[i][0] as int;
            let a1 = first[i][1] as int;
            let b0 = second[j][0] as int;
            let b1 = second[j][1] as int;
            let lo = Self::max_int(a0, b0);
            let hi = Self::min_int(a1, b1);
            if rest.len() > 0 {
                Self::lemma_intersection_list_first_element_bounds(first, second, i2, j2);
                let next_start = rest[0][0] as int;
                assert(next_start >= first[i2][0] as int);
                assert(next_start >= second[j2][0] as int);
                if (first[i][1] as int) < (second[j][1] as int) {
                    assert(i2 == i + 1);
                    assert(j2 == j);
                    assert(i as int + 1 < first.len());
                    Self::lemma_sorted_disjoint_index(first, i);
                    assert(first[i + 1][0] as int > a1);
                    if lo <= hi {
                        assert(hi <= a1);
                        assert(lo <= a1);
                        assert(lo <= next_start);
                    }
                } else {
                    assert(j2 == j + 1);
                    assert(i2 == i);
                    assert(j as int + 1 < second.len());
                    Self::lemma_sorted_disjoint_index(second, j);
                    assert(second[j + 1][0] as int > b1);
                    if lo <= hi {
                        assert(hi <= b1);
                        assert(lo <= b1);
                        assert(lo <= next_start);
                    }
                }
            }
        }
    }

    pub proof fn lemma_sorted_disjoint_index(
        first: Seq<Vec<i32>>,
        i: int,
    )
        requires
            Self::sorted_disjoint(first),
            0 <= i < first.len() as int - 1,
        ensures
            first[i][1] < first[i + 1][0],
    {
        assert(Self::disjoint_at(first, i));
    }

    pub proof fn lemma_intersection_list_first_element_bounds(
        first: Seq<Vec<i32>>,
        second: Seq<Vec<i32>>,
        i: int,
        j: int,
    )
        requires
            0 <= i < first.len(),
            0 <= j < second.len(),
            Self::sorted_disjoint(first),
            Self::sorted_disjoint(second),
            Self::intersection_list(first, second, i, j).len() > 0,
        ensures
            Self::intersection_list(first, second, i, j)[0][0] as int >= first[i][0] as int,
            Self::intersection_list(first, second, i, j)[0][0] as int >= second[j][0] as int,
        decreases
            (first.len() - i) + (second.len() - j),
    {
        reveal_with_fuel(Solution::intersection_list, 1);
        let a0 = first[i][0] as int;
        let a1 = first[i][1] as int;
        let b0 = second[j][0] as int;
        let b1 = second[j][1] as int;
        let lo = Self::max_int(a0, b0);
        let hi = Self::min_int(a1, b1);
        let (i2, j2) = (
            if (first[i][1] as int) < (second[j][1] as int) { i + 1 } else { i },
            if (first[i][1] as int) < (second[j][1] as int) { j } else { j + 1 },
        );
        let rest = Self::intersection_list(first, second, i2, j2);
        if lo <= hi {
            assert(Self::intersection_list(first, second, i, j)[0][0] == lo as i32);
            assert(lo >= a0);
            assert(lo >= b0);
        } else {
            assert(Self::intersection_list(first, second, i, j) =~= rest);
            assert(rest.len() > 0);
            Self::lemma_intersection_list_first_element_bounds(first, second, i2, j2);
            assert(rest[0][0] as int >= first[i2][0] as int);
            assert(rest[0][0] as int >= second[j2][0] as int);
            if (first[i][1] as int) < (second[j][1] as int) {
                assert(i2 == i + 1);
                assert(i as int + 1 < first.len());
                Self::lemma_sorted_disjoint_index(first, i);
                assert(first[i + 1][0] as int > a1);
                assert(Self::valid_interval(first, i));
                assert(a0 < a1);
                assert(first[i + 1][0] as int >= a0);
            } else {
                assert(j2 == j + 1);
                assert(j as int + 1 < second.len());
                Self::lemma_sorted_disjoint_index(second, j);
                assert(second[j + 1][0] as int > b1);
                assert(Self::valid_interval(second, j));
                assert(b0 < b1);
                assert(second[j + 1][0] as int >= b0);
            }
        }
    }

    pub proof fn lemma_intersection_list_step(
        first: Seq<Vec<i32>>,
        second: Seq<Vec<i32>>,
        i: int,
        j: int,
    )
        requires
            0 <= i < first.len(),
            0 <= j < second.len(),
            Self::max_int(first[i][0] as int, second[j][0] as int)
                <= Self::min_int(first[i][1] as int, second[j][1] as int),
        ensures
            Self::intersection_list(first, second, i, j).len() > 0,
            Self::intersection_list(first, second, i, j)[0][0]
                == Self::max_int(first[i][0] as int, second[j][0] as int) as i32,
            Self::intersection_list(first, second, i, j)[0][1]
                == Self::min_int(first[i][1] as int, second[j][1] as int) as i32,
            Self::intersection_list(first, second, i, j).subrange(
                1,
                Self::intersection_list(first, second, i, j).len() as int,
            ) =~= Self::intersection_list(
                first,
                second,
                if (first[i][1] as int) < (second[j][1] as int) { i + 1 } else { i },
                if (first[i][1] as int) < (second[j][1] as int) { j } else { j + 1 },
            ),
    {
        reveal_with_fuel(Solution::intersection_list, 2);
    }

    #[verifier::exec_allows_no_decreases_clause]
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
        let ghost full = Self::intersection_list(first_list@, second_list@, 0, 0);
        proof {
            Self::lemma_intersection_list_sorted(first_list@, second_list@, 0, 0);
        }
        while i < n && j < m
            invariant
                0 <= first_list.len() <= 1000,
                0 <= second_list.len() <= 1000,
                n == first_list.len(),
                m == second_list.len(),
                Self::interval_rows(first_list@),
                Self::interval_rows(second_list@),
                i <= n,
                j <= m,
                result@.len() <= full.len(),
                forall |k: int| 0 <= k < full.len() as int - 1 ==> #[trigger] full[k][0] <= full[k + 1][0],
                result@.len() + Self::intersection_list(first_list@, second_list@, i as int, j as int).len()
                    == full.len(),
                forall |k: int| 0 <= k < result@.len() ==>
                    result@[k][0] == full[k][0] && result@[k][1] == full[k][1],
                forall |k: int| 0 <= k < Self::intersection_list(first_list@, second_list@, i as int, j as int).len() ==>
                    full[result@.len() as int + k][0] == Self::intersection_list(first_list@, second_list@, i as int, j as int)[k][0]
                    && full[result@.len() as int + k][1] == Self::intersection_list(first_list@, second_list@, i as int, j as int)[k][1],
                forall |k: int| 0 <= k < result@.len() ==>
                    result@[k].len() == 2 && result@[k][0] <= result@[k][1],
                forall |k: int| 0 <= k < result@.len() as int - 1 ==>
                    #[trigger] result@[k][0] <= result@[k + 1][0],
            decreases
                (n - i) + (m - j),
        {
            proof {
                assert(i < n);
                assert(j < m);
                assert(Self::interval_rows(first_list@));
                assert(first_list@[i as int].len() == 2);
                assert(second_list@[j as int].len() == 2);
            }
            let ghost rest = Self::intersection_list(first_list@, second_list@, i as int, j as int);
            let lo = first_list[i][0].max(second_list[j][0]);
            let hi = first_list[i][1].min(second_list[j][1]);
            let ghost old_len = result@.len();
            let ghost i_old = i as int;
            let ghost j_old = j as int;
            if lo <= hi {
                result.push(vec![lo, hi]);
            }
            if first_list[i][1] < second_list[j][1] {
                i += 1;
            } else {
                j += 1;
            }
            proof {
                let rest_old = Self::intersection_list(first_list@, second_list@, i_old, j_old);
                let rest_new = Self::intersection_list(first_list@, second_list@, i as int, j as int);
                if lo <= hi {
                    Self::lemma_intersection_list_step(first_list@, second_list@, i_old, j_old);
                    assert(rest_old.subrange(1, rest_old.len() as int) =~= rest_new);
                    assert forall |k: int| 0 <= k < rest_new.len() implies
                        full[old_len as int + 1 + k][0] == rest_new[k][0]
                        && full[old_len as int + 1 + k][1] == rest_new[k][1] by {
                        assert(rest_old[1 + k][0] == rest_new[k][0]);
                        assert(rest_old[1 + k][1] == rest_new[k][1]);
                        assert(full[old_len as int + 1 + k][0] == rest_old[1 + k][0]);
                        assert(full[old_len as int + 1 + k][1] == rest_old[1 + k][1]);
                    };
                } else {
                    assert(rest_old =~= rest_new);
                }
                assert forall |k: int| 0 <= k < result@.len() as int - 1 implies
                    #[trigger] result@[k][0] <= result@[k + 1][0]
                by {
                    assert(result@[k][0] == full[k][0]);
                    assert(result@[k + 1][0] == full[k + 1][0]);
                };
            }
        }
        result
    }
}

}