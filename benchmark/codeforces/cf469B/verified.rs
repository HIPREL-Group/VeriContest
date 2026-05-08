use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_schedule(starts: Seq<i32>, ends: Seq<i32>) -> bool {
        1 <= starts.len() <= 50
            && starts.len() == ends.len()
            && forall|i: int| 0 <= i < starts.len() ==> 0 <= #[trigger] starts[i] < #[trigger] ends[i] <= 1000
    }

    pub open spec fn intervals_overlap_at_shift(
        z_starts: Seq<i32>,
        z_ends: Seq<i32>,
        x_starts: Seq<i32>,
        x_ends: Seq<i32>,
        i: int,
        j: int,
        t: int,
    ) -> bool
        recommends
            0 <= i < z_starts.len(),
            0 <= j < x_starts.len(),
            z_starts.len() == z_ends.len(),
            x_starts.len() == x_ends.len(),
    {
        x_starts[j] + t <= z_ends[i] && z_starts[i] <= x_ends[j] + t
    }

    pub open spec fn suitable_shift(
        z_starts: Seq<i32>,
        z_ends: Seq<i32>,
        x_starts: Seq<i32>,
        x_ends: Seq<i32>,
        t: int,
    ) -> bool
        recommends
            z_starts.len() == z_ends.len(),
            x_starts.len() == x_ends.len(),
    {
        exists|i: int, j: int|
            0 <= i < z_starts.len()
                && 0 <= j < x_starts.len()
                && #[trigger] Self::intervals_overlap_at_shift(z_starts, z_ends, x_starts, x_ends, i, j, t)
    }

    pub open spec fn count_suitable_shifts(
        z_starts: Seq<i32>,
        z_ends: Seq<i32>,
        x_starts: Seq<i32>,
        x_ends: Seq<i32>,
        l: int,
        upto: int,
    ) -> int
        recommends
            l <= upto,
            z_starts.len() == z_ends.len(),
            x_starts.len() == x_ends.len(),
        decreases upto - l,
    {
        if upto <= l {
            0
        } else {
            Self::count_suitable_shifts(z_starts, z_ends, x_starts, x_ends, l, upto - 1)
                + if Self::suitable_shift(z_starts, z_ends, x_starts, x_ends, upto - 1) {
                    1int
                } else {
                    0int
                }
        }
    }

    pub fn count_chat_times(
        z_starts: Vec<i32>,
        z_ends: Vec<i32>,
        x_starts: Vec<i32>,
        x_ends: Vec<i32>,
        l: i32,
        r: i32,
    ) -> (result: i32)
        requires
            Self::valid_schedule(z_starts@, z_ends@),
            Self::valid_schedule(x_starts@, x_ends@),
            0 <= l <= r <= 1000,
        ensures
            result as int == Self::count_suitable_shifts(z_starts@, z_ends@, x_starts@, x_ends@, l as int, r as int + 1),
    {
        let mut result = 0i32;
        let mut t = l;
        while t <= r
            invariant
                Self::valid_schedule(z_starts@, z_ends@),
                Self::valid_schedule(x_starts@, x_ends@),
                0 <= l <= r <= 1000,
                l <= t <= r + 1,
                0 <= result <= t - l,
                result as int == Self::count_suitable_shifts(z_starts@, z_ends@, x_starts@, x_ends@, l as int, t as int),
            decreases
                r as int - t as int + 1,
        {
            let mut found = false;
            let mut i = 0usize;
            while i < z_starts.len() && !found
                invariant
                    Self::valid_schedule(z_starts@, z_ends@),
                    Self::valid_schedule(x_starts@, x_ends@),
                    0 <= l <= r <= 1000,
                    l <= t <= r,
                    0 <= i <= z_starts.len(),
                    !found ==> forall|ii: int, jj: int|
                        0 <= ii < i && 0 <= jj < x_starts.len() ==>
                            !#[trigger] Self::intervals_overlap_at_shift(z_starts@, z_ends@, x_starts@, x_ends@, ii, jj, t as int),
                    found ==> Self::suitable_shift(z_starts@, z_ends@, x_starts@, x_ends@, t as int),
                decreases
                    (if found { 0int } else { 1int }),
                    z_starts.len() as int - i as int,
            {
                let mut j = 0usize;
                while j < x_starts.len() && !found
                    invariant
                        Self::valid_schedule(z_starts@, z_ends@),
                        Self::valid_schedule(x_starts@, x_ends@),
                        0 <= l <= r <= 1000,
                        l <= t <= r,
                        i < z_starts.len(),
                        0 <= j <= x_starts.len(),
                        !found ==> forall|ii: int, jj: int|
                            0 <= ii < i && 0 <= jj < x_starts.len() ==>
                                !#[trigger] Self::intervals_overlap_at_shift(z_starts@, z_ends@, x_starts@, x_ends@, ii, jj, t as int),
                        !found ==> forall|jj: int|
                            0 <= jj < j ==>
                                !#[trigger] Self::intervals_overlap_at_shift(z_starts@, z_ends@, x_starts@, x_ends@, i as int, jj, t as int),
                        found ==> Self::suitable_shift(z_starts@, z_ends@, x_starts@, x_ends@, t as int),
                    decreases
                        (if found { 0int } else { 1int }),
                        x_starts.len() as int - j as int,
                {
                    let zs = z_starts[i];
                    let ze = z_ends[i];
                    let xs = x_starts[j];
                    let xe = x_ends[j];
                    proof {
                        assert(zs as int == z_starts@[i as int]);
                        assert(ze as int == z_ends@[i as int]);
                        assert(xs as int == x_starts@[j as int]);
                        assert(xe as int == x_ends@[j as int]);
                        assert(0 <= xs <= 1000);
                        assert(0 <= xe <= 1000);
                        assert(0 <= t <= 1000);
                        assert(xs + t <= 2000);
                        assert(xe + t <= 2000);
                    }
                    if xs + t <= ze && zs <= xe + t {
                        proof {
                            assert(Self::intervals_overlap_at_shift(z_starts@, z_ends@, x_starts@, x_ends@, i as int, j as int, t as int));
                            assert(Self::suitable_shift(z_starts@, z_ends@, x_starts@, x_ends@, t as int));
                        }
                        found = true;
                    } else {
                        proof {
                            assert(!Self::intervals_overlap_at_shift(z_starts@, z_ends@, x_starts@, x_ends@, i as int, j as int, t as int));
                        }
                        j += 1;
                    }
                }
                if !found {
                    proof {
                        assert(j == x_starts.len());
                        assert(forall|jj: int|
                            0 <= jj < x_starts.len() ==>
                                !#[trigger] Self::intervals_overlap_at_shift(z_starts@, z_ends@, x_starts@, x_ends@, i as int, jj, t as int));
                        assert forall|ii: int, jj: int|
                            0 <= ii < i + 1 && 0 <= jj < x_starts.len() implies
                                !#[trigger] Self::intervals_overlap_at_shift(z_starts@, z_ends@, x_starts@, x_ends@, ii, jj, t as int) by {
                            if ii < i {
                                assert(!Self::intervals_overlap_at_shift(z_starts@, z_ends@, x_starts@, x_ends@, ii, jj, t as int));
                            } else {
                                assert(ii == i);
                                assert(!Self::intervals_overlap_at_shift(z_starts@, z_ends@, x_starts@, x_ends@, i as int, jj, t as int));
                            }
                        }
                    }
                    i += 1;
                }
            }
            if found {
                proof {
                    assert(Self::suitable_shift(z_starts@, z_ends@, x_starts@, x_ends@, t as int));
                }
            } else {
                proof {
                    assert(i == z_starts.len());
                    assert(forall|ii: int, jj: int|
                        0 <= ii < z_starts.len() && 0 <= jj < x_starts.len() ==>
                            !#[trigger] Self::intervals_overlap_at_shift(z_starts@, z_ends@, x_starts@, x_ends@, ii, jj, t as int));
                    assert(!Self::suitable_shift(z_starts@, z_ends@, x_starts@, x_ends@, t as int));
                }
            }
            let prev_result = result;
            if found {
                proof {
                    assert(0 <= result <= t - l);
                    assert(t - l <= 1000);
                    assert(result < i32::MAX);
                }
                result += 1;
            }
            proof {
                assert(Self::count_suitable_shifts(z_starts@, z_ends@, x_starts@, x_ends@, l as int, t as int + 1)
                    == Self::count_suitable_shifts(z_starts@, z_ends@, x_starts@, x_ends@, l as int, t as int)
                        + if Self::suitable_shift(z_starts@, z_ends@, x_starts@, x_ends@, t as int) { 1int } else { 0int });
                if found {
                    assert(result == prev_result + 1);
                    assert(Self::suitable_shift(z_starts@, z_ends@, x_starts@, x_ends@, t as int));
                    assert(result as int
                        == Self::count_suitable_shifts(z_starts@, z_ends@, x_starts@, x_ends@, l as int, t as int + 1));
                } else {
                    assert(result == prev_result);
                    assert(!Self::suitable_shift(z_starts@, z_ends@, x_starts@, x_ends@, t as int));
                    assert(result as int
                        == Self::count_suitable_shifts(z_starts@, z_ends@, x_starts@, x_ends@, l as int, t as int + 1));
                }
            }
            t += 1;
        }
        result
    }
}

}
