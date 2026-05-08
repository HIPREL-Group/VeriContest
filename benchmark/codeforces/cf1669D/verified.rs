use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_color(c: int) -> bool {
        c == 0 || c == 1 || c == 2
    }

    pub open spec fn segment_non_white(s: Seq<i32>, l: int, r: int) -> bool {
        forall|k: int| l <= k < r ==> #[trigger] s[k] != 0
    }

    pub open spec fn segment_has_color(s: Seq<i32>, l: int, r: int, color: int) -> bool {
        exists|k: int| l <= k < r && s[k] as int == color
    }

    pub open spec fn good_segment(s: Seq<i32>, l: int, r: int) -> bool {
        0 <= l < r <= s.len()
            && (l == 0 || s[l - 1] == 0)
            && (r == s.len() || s[r] == 0)
            && Self::segment_non_white(s, l, r)
    }

    pub open spec fn valid_picture(s: Seq<i32>) -> bool {
        forall|l: int, r: int|
            Self::good_segment(s, l, r)
                ==> Self::segment_has_color(s, l, r, 1)
                    && Self::segment_has_color(s, l, r, 2)
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn possible_picture(cells: Vec<i32>) -> (res: bool)
        requires
            1 <= cells.len() <= 100000,
            forall|k: int| 0 <= k < cells.len() as int ==> Self::is_color(#[trigger] cells[k] as int),
        ensures
            res == Self::valid_picture(cells@),
    {
        let n = cells.len();
        let mut i: usize = 0;

        while i < n
            invariant
                n == cells.len(),
                1 <= n <= 100000,
                0 <= i <= n,
                i == 0 || i == n || cells[i as int] == 0,
                forall|k: int| 0 <= k < cells.len() as int ==> Self::is_color(#[trigger] cells[k] as int),
                forall|l: int, r: int|
                    Self::good_segment(cells@, l, r) && r <= i as int
                        ==> Self::segment_has_color(cells@, l, r, 1)
                            && Self::segment_has_color(cells@, l, r, 2),
            decreases n - i,
        {
            let pre = i;
            while i < n && cells[i] == 0
                invariant
                    n == cells.len(),
                    1 <= n <= 100000,
                    pre <= i <= n,
                    forall|k: int| pre as int <= k < i as int ==> #[trigger] cells[k] == 0,
                    forall|k: int| 0 <= k < cells.len() as int ==> Self::is_color(#[trigger] cells[k] as int),
                    forall|l: int, r: int|
                        Self::good_segment(cells@, l, r) && r <= i as int
                            ==> Self::segment_has_color(cells@, l, r, 1)
                                && Self::segment_has_color(cells@, l, r, 2),
                decreases n - i,
            {
                i = i + 1;
            }

            if i < n {
                assert(cells[i as int] != 0);
                if i == pre {
                    assert(pre == 0);
                } else {
                    assert(pre < i);
                    assert(cells[i as int - 1] == 0);
                }

                let start = i;
                let mut has_r = false;
                let mut has_b = false;

                while i < n && cells[i] != 0
                invariant
                    n == cells.len(),
                    1 <= n <= 100000,
                    start <= i <= n,
                    start < n,
                    cells[start as int] != 0,
                    start == 0 || cells[start as int - 1] == 0,
                    forall|k: int| 0 <= k < cells.len() as int ==> Self::is_color(#[trigger] cells[k] as int),
                    forall|l: int, r: int|
                        Self::good_segment(cells@, l, r) && r <= start as int
                            ==> Self::segment_has_color(cells@, l, r, 1)
                                && Self::segment_has_color(cells@, l, r, 2),
                    forall|k: int| start as int <= k < i as int ==> #[trigger] cells[k] != 0,
                    has_r ==> Self::segment_has_color(cells@, start as int, i as int, 1),
                    !has_r ==> forall|k: int| start as int <= k < i as int ==> cells[k] != 1,
                    has_b ==> Self::segment_has_color(cells@, start as int, i as int, 2),
                    !has_b ==> forall|k: int| start as int <= k < i as int ==> cells[k] != 2,
                decreases n - i,
                {
                    if cells[i] == 1 {
                        has_r = true;
                    }
                    if cells[i] == 2 {
                        has_b = true;
                    }
                    let x = cells[i];
                    i = i + 1;

                    proof {
                        if has_r {
                            if x == 1 {
                                assert(cells[i as int - 1] == 1);
                                assert(Self::segment_has_color(cells@, start as int, i as int, 1));
                            } else {
                                assert(Self::segment_has_color(cells@, start as int, i as int - 1, 1));
                                assert(Self::segment_has_color(cells@, start as int, i as int, 1));
                            }
                        }
                        if !has_r {
                            assert forall|k: int| start as int <= k < i as int implies cells[k] != 1 by {
                                if k == i as int - 1 {
                                    assert(cells[k] != 1);
                                } else {
                                    assert(start as int <= k < i as int - 1);
                                }
                            };
                        }

                        if has_b {
                            if x == 2 {
                                assert(cells[i as int - 1] == 2);
                                assert(Self::segment_has_color(cells@, start as int, i as int, 2));
                            } else {
                                assert(Self::segment_has_color(cells@, start as int, i as int - 1, 2));
                                assert(Self::segment_has_color(cells@, start as int, i as int, 2));
                            }
                        }
                        if !has_b {
                            assert forall|k: int| start as int <= k < i as int implies cells[k] != 2 by {
                                if k == i as int - 1 {
                                    assert(cells[k] != 2);
                                } else {
                                    assert(start as int <= k < i as int - 1);
                                }
                            };
                        }
                    }
                }

                if !(has_r && has_b) {
                    proof {
                        let l = start as int;
                        let r = i as int;
                        assert(0 <= l < r <= cells@.len());
                        assert(l == 0 || cells[l - 1] == 0);
                        assert(r == cells@.len() || cells[r] == 0);
                        assert(Self::segment_non_white(cells@, l, r));
                        assert(Self::good_segment(cells@, l, r));

                        if !has_r {
                            assert(!Self::segment_has_color(cells@, l, r, 1));
                        }
                        if !has_b {
                            assert(!Self::segment_has_color(cells@, l, r, 2));
                        }
                        assert(!(Self::segment_has_color(cells@, l, r, 1)
                            && Self::segment_has_color(cells@, l, r, 2)));

                        if Self::valid_picture(cells@) {
                            assert(Self::segment_has_color(cells@, l, r, 1)
                                && Self::segment_has_color(cells@, l, r, 2));
                        }
                        assert(!Self::valid_picture(cells@));
                    }
                    return false;
                }

                proof {
                    assert(start < i);
                    assert(Self::segment_has_color(cells@, start as int, i as int, 1));
                    assert(Self::segment_has_color(cells@, start as int, i as int, 2));
                    assert(i == cells@.len() || cells[i as int] == 0);

                    assert forall|l: int, r: int|
                        Self::good_segment(cells@, l, r) && r <= i as int
                            implies Self::segment_has_color(cells@, l, r, 1)
                                && Self::segment_has_color(cells@, l, r, 2) by {
                        if r <= start as int {
                        } else {
                            assert((start as int) < r);
                            assert(r <= (i as int));
                            assert(r == (i as int));
                            assert((start as int) <= l);
                            assert(l < r);
                            assert(l == (start as int));
                        }
                    };
                }
            }
        }

        proof {
            assert(i == n);
            assert forall|l: int, r: int|
                Self::good_segment(cells@, l, r)
                    implies Self::segment_has_color(cells@, l, r, 1)
                        && Self::segment_has_color(cells@, l, r, 2) by {
                assert(r <= i as int);
            };
        }

        true
    }
}

}
