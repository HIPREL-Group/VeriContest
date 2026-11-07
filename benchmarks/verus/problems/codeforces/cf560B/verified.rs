use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn oriented_width(a: int, b: int, rotated: bool) -> int {
    if rotated { b } else { a }
}

pub open spec fn oriented_height(a: int, b: int, rotated: bool) -> int {
    if rotated { a } else { b }
}

pub open spec fn fits_in(container_w: int, container_h: int, rect_w: int, rect_h: int) -> bool {
    0 <= rect_w && rect_w <= container_w && 0 <= rect_h && rect_h <= container_h
}

pub open spec fn vertical_split_possible(
    board_w: int,
    board_h: int,
    rect2_w: int,
    rect2_h: int,
    rect3_w: int,
    rect3_h: int,
) -> bool {
    exists|cut: int|
        0 <= cut <= board_w
            && fits_in(cut, board_h, rect2_w, rect2_h)
            && fits_in(board_w - cut, board_h, rect3_w, rect3_h)
}

pub open spec fn horizontal_split_possible(
    board_w: int,
    board_h: int,
    rect2_w: int,
    rect2_h: int,
    rect3_w: int,
    rect3_h: int,
) -> bool {
    exists|cut: int|
        0 <= cut <= board_h
            && fits_in(board_w, cut, rect2_w, rect2_h)
            && fits_in(board_w, board_h - cut, rect3_w, rect3_h)
}

pub open spec fn placement_with_orientations(
    board_w: int,
    board_h: int,
    a2: int,
    b2: int,
    a3: int,
    b3: int,
    rot2: bool,
    rot3: bool,
) -> bool {
    vertical_split_possible(
        board_w,
        board_h,
        oriented_width(a2, b2, rot2),
        oriented_height(a2, b2, rot2),
        oriented_width(a3, b3, rot3),
        oriented_height(a3, b3, rot3),
    ) || horizontal_split_possible(
        board_w,
        board_h,
        oriented_width(a2, b2, rot2),
        oriented_height(a2, b2, rot2),
        oriented_width(a3, b3, rot3),
        oriented_height(a3, b3, rot3),
    )
}

pub open spec fn simplified_fit_for_dims(
    board_w: int,
    board_h: int,
    rect2_w: int,
    rect2_h: int,
    rect3_w: int,
    rect3_h: int,
) -> bool {
    (rect2_w + rect3_w <= board_w && rect2_h <= board_h && rect3_h <= board_h)
        || (rect2_w <= board_w && rect3_w <= board_w && rect2_h + rect3_h <= board_h)
}

pub open spec fn simplified_fit_with_orientations(
    board_w: int,
    board_h: int,
    a2: int,
    b2: int,
    a3: int,
    b3: int,
    rot2: bool,
    rot3: bool,
) -> bool {
    simplified_fit_for_dims(
        board_w,
        board_h,
        oriented_width(a2, b2, rot2),
        oriented_height(a2, b2, rot2),
        oriented_width(a3, b3, rot3),
        oriented_height(a3, b3, rot3),
    )
}

pub open spec fn can_place_paintings_cases(
    board_w: int,
    board_h: int,
    a2: int,
    b2: int,
    a3: int,
    b3: int,
) -> bool {
    placement_with_orientations(board_w, board_h, a2, b2, a3, b3, false, false)
        || placement_with_orientations(board_w, board_h, a2, b2, a3, b3, false, true)
        || placement_with_orientations(board_w, board_h, a2, b2, a3, b3, true, false)
        || placement_with_orientations(board_w, board_h, a2, b2, a3, b3, true, true)
}

pub open spec fn can_place_paintings_spec(
    board_w: int,
    board_h: int,
    a2: int,
    b2: int,
    a3: int,
    b3: int,
) -> bool {
    exists|rot2: bool, rot3: bool| placement_with_orientations(board_w, board_h, a2, b2, a3, b3, rot2, rot3)
}

proof fn lemma_vertical_sum_implies_split(
    board_w: int,
    board_h: int,
    rect2_w: int,
    rect2_h: int,
    rect3_w: int,
    rect3_h: int,
)
    requires
        0 <= board_w,
        0 <= board_h,
        0 <= rect2_w,
        0 <= rect2_h,
        0 <= rect3_w,
        0 <= rect3_h,
        rect2_w + rect3_w <= board_w,
        rect2_h <= board_h,
        rect3_h <= board_h,
    ensures
        vertical_split_possible(board_w, board_h, rect2_w, rect2_h, rect3_w, rect3_h),
{
    let cut = rect2_w;
    assert(0 <= cut);
    assert(rect2_w <= board_w) by (nonlinear_arith)
        requires
            0 <= rect3_w,
            rect2_w + rect3_w <= board_w;
    assert(cut <= board_w);
    assert(0 <= cut <= board_w);
    assert(fits_in(cut, board_h, rect2_w, rect2_h));
    assert(fits_in(board_w - cut, board_h, rect3_w, rect3_h));
}

proof fn lemma_vertical_split_implies_sum(
    board_w: int,
    board_h: int,
    rect2_w: int,
    rect2_h: int,
    rect3_w: int,
    rect3_h: int,
)
    requires
        0 <= board_w,
        0 <= board_h,
        0 <= rect2_w,
        0 <= rect2_h,
        0 <= rect3_w,
        0 <= rect3_h,
        vertical_split_possible(board_w, board_h, rect2_w, rect2_h, rect3_w, rect3_h),
    ensures
        rect2_w + rect3_w <= board_w,
        rect2_h <= board_h,
        rect3_h <= board_h,
{
    let cut = choose|cut: int|
        0 <= cut <= board_w
            && fits_in(cut, board_h, rect2_w, rect2_h)
            && fits_in(board_w - cut, board_h, rect3_w, rect3_h);
    assert(rect2_w <= cut);
    assert(rect3_w <= board_w - cut);
    assert(rect2_w + rect3_w <= board_w) by (nonlinear_arith)
        requires
            rect2_w <= cut,
            rect3_w <= board_w - cut;
    assert(rect2_h <= board_h);
    assert(rect3_h <= board_h);
}

proof fn lemma_horizontal_sum_implies_split(
    board_w: int,
    board_h: int,
    rect2_w: int,
    rect2_h: int,
    rect3_w: int,
    rect3_h: int,
)
    requires
        0 <= board_w,
        0 <= board_h,
        0 <= rect2_w,
        0 <= rect2_h,
        0 <= rect3_w,
        0 <= rect3_h,
        rect2_w <= board_w,
        rect3_w <= board_w,
        rect2_h + rect3_h <= board_h,
    ensures
        horizontal_split_possible(board_w, board_h, rect2_w, rect2_h, rect3_w, rect3_h),
{
    let cut = rect2_h;
    assert(0 <= cut);
    assert(rect2_h <= board_h) by (nonlinear_arith)
        requires
            0 <= rect3_h,
            rect2_h + rect3_h <= board_h;
    assert(cut <= board_h);
    assert(0 <= cut <= board_h);
    assert(fits_in(board_w, cut, rect2_w, rect2_h));
    assert(fits_in(board_w, board_h - cut, rect3_w, rect3_h));
}

proof fn lemma_horizontal_split_implies_sum(
    board_w: int,
    board_h: int,
    rect2_w: int,
    rect2_h: int,
    rect3_w: int,
    rect3_h: int,
)
    requires
        0 <= board_w,
        0 <= board_h,
        0 <= rect2_w,
        0 <= rect2_h,
        0 <= rect3_w,
        0 <= rect3_h,
        horizontal_split_possible(board_w, board_h, rect2_w, rect2_h, rect3_w, rect3_h),
    ensures
        rect2_w <= board_w,
        rect3_w <= board_w,
        rect2_h + rect3_h <= board_h,
{
    let cut = choose|cut: int|
        0 <= cut <= board_h
            && fits_in(board_w, cut, rect2_w, rect2_h)
            && fits_in(board_w, board_h - cut, rect3_w, rect3_h);
    assert(rect2_h <= cut);
    assert(rect3_h <= board_h - cut);
    assert(rect2_h + rect3_h <= board_h) by (nonlinear_arith)
        requires
            rect2_h <= cut,
            rect3_h <= board_h - cut;
    assert(rect2_w <= board_w);
    assert(rect3_w <= board_w);
}

proof fn lemma_placement_equiv_simplified(
    board_w: int,
    board_h: int,
    rect2_w: int,
    rect2_h: int,
    rect3_w: int,
    rect3_h: int,
)
    requires
        0 <= board_w,
        0 <= board_h,
        0 <= rect2_w,
        0 <= rect2_h,
        0 <= rect3_w,
        0 <= rect3_h,
    ensures
        placement_with_orientations(board_w, board_h, rect2_w, rect2_h, rect3_w, rect3_h, false, false)
            == simplified_fit_for_dims(board_w, board_h, rect2_w, rect2_h, rect3_w, rect3_h),
{
    if placement_with_orientations(board_w, board_h, rect2_w, rect2_h, rect3_w, rect3_h, false, false) {
        if vertical_split_possible(board_w, board_h, rect2_w, rect2_h, rect3_w, rect3_h) {
            lemma_vertical_split_implies_sum(board_w, board_h, rect2_w, rect2_h, rect3_w, rect3_h);
        } else {
            lemma_horizontal_split_implies_sum(board_w, board_h, rect2_w, rect2_h, rect3_w, rect3_h);
        }
    } else if simplified_fit_for_dims(board_w, board_h, rect2_w, rect2_h, rect3_w, rect3_h) {
        if rect2_w + rect3_w <= board_w && rect2_h <= board_h && rect3_h <= board_h {
            lemma_vertical_sum_implies_split(board_w, board_h, rect2_w, rect2_h, rect3_w, rect3_h);
        } else {
            lemma_horizontal_sum_implies_split(board_w, board_h, rect2_w, rect2_h, rect3_w, rect3_h);
        }
    }
}

proof fn lemma_cases_equiv_spec(
    board_w: int,
    board_h: int,
    a2: int,
    b2: int,
    a3: int,
    b3: int,
)
    ensures
        can_place_paintings_cases(board_w, board_h, a2, b2, a3, b3)
            == can_place_paintings_spec(board_w, board_h, a2, b2, a3, b3),
{
    if can_place_paintings_cases(board_w, board_h, a2, b2, a3, b3) {
        if placement_with_orientations(board_w, board_h, a2, b2, a3, b3, false, false) {
            assert(exists|rot2: bool, rot3: bool|
                placement_with_orientations(board_w, board_h, a2, b2, a3, b3, rot2, rot3)) by {
                assert(placement_with_orientations(board_w, board_h, a2, b2, a3, b3, false, false));
            }
        } else if placement_with_orientations(board_w, board_h, a2, b2, a3, b3, false, true) {
            assert(exists|rot2: bool, rot3: bool|
                placement_with_orientations(board_w, board_h, a2, b2, a3, b3, rot2, rot3)) by {
                assert(placement_with_orientations(board_w, board_h, a2, b2, a3, b3, false, true));
            }
        } else if placement_with_orientations(board_w, board_h, a2, b2, a3, b3, true, false) {
            assert(exists|rot2: bool, rot3: bool|
                placement_with_orientations(board_w, board_h, a2, b2, a3, b3, rot2, rot3)) by {
                assert(placement_with_orientations(board_w, board_h, a2, b2, a3, b3, true, false));
            }
        } else {
            assert(placement_with_orientations(board_w, board_h, a2, b2, a3, b3, true, true));
            assert(exists|rot2: bool, rot3: bool|
                placement_with_orientations(board_w, board_h, a2, b2, a3, b3, rot2, rot3)) by {
                assert(placement_with_orientations(board_w, board_h, a2, b2, a3, b3, true, true));
            }
        }
    } else {
        assert forall|rot2: bool, rot3: bool|
            !placement_with_orientations(board_w, board_h, a2, b2, a3, b3, rot2, rot3) by {
            if !rot2 && !rot3 {
                assert(!placement_with_orientations(board_w, board_h, a2, b2, a3, b3, false, false));
            } else if !rot2 && rot3 {
                assert(!placement_with_orientations(board_w, board_h, a2, b2, a3, b3, false, true));
            } else if rot2 && !rot3 {
                assert(!placement_with_orientations(board_w, board_h, a2, b2, a3, b3, true, false));
            } else {
                assert(!placement_with_orientations(board_w, board_h, a2, b2, a3, b3, true, true));
            }
        };
        assert(!can_place_paintings_spec(board_w, board_h, a2, b2, a3, b3));
    }
}

impl Solution {
    pub fn can_place_paintings(a1: i32, b1: i32, a2: i32, b2: i32, a3: i32, b3: i32) -> (res: bool)
        requires
            1 <= a1 <= 1000,
            1 <= b1 <= 1000,
            1 <= a2 <= 1000,
            1 <= b2 <= 1000,
            1 <= a3 <= 1000,
            1 <= b3 <= 1000,
        ensures
            res == can_place_paintings_spec(a1 as int, b1 as int, a2 as int, b2 as int, a3 as int, b3 as int),
    {
        let check1 = a2 + a3 <= a1 && b2 <= b1 && b3 <= b1;
        let check2 = a2 + b3 <= a1 && b2 <= b1 && a3 <= b1;
        let check3 = b2 + a3 <= a1 && a2 <= b1 && b3 <= b1;
        let check4 = b2 + b3 <= a1 && a2 <= b1 && a3 <= b1;
        let check5 = a2 <= a1 && a3 <= a1 && b2 + b3 <= b1;
        let check6 = a2 <= a1 && b3 <= a1 && b2 + a3 <= b1;
        let check7 = b2 <= a1 && a3 <= a1 && a2 + b3 <= b1;
        let check8 = b2 <= a1 && b3 <= a1 && a2 + a3 <= b1;
        let result = check1 || check2 || check3 || check4 || check5 || check6 || check7 || check8;
        proof {
            lemma_placement_equiv_simplified(a1 as int, b1 as int, a2 as int, b2 as int, a3 as int, b3 as int);
            lemma_placement_equiv_simplified(a1 as int, b1 as int, a2 as int, b2 as int, b3 as int, a3 as int);
            lemma_placement_equiv_simplified(a1 as int, b1 as int, b2 as int, a2 as int, a3 as int, b3 as int);
            lemma_placement_equiv_simplified(a1 as int, b1 as int, b2 as int, a2 as int, b3 as int, a3 as int);
            lemma_cases_equiv_spec(a1 as int, b1 as int, a2 as int, b2 as int, a3 as int, b3 as int);
            assert(
                placement_with_orientations(a1 as int, b1 as int, a2 as int, b2 as int, a3 as int, b3 as int, false, false)
                    == (check1 || check5)
            );
            assert(
                placement_with_orientations(a1 as int, b1 as int, a2 as int, b2 as int, a3 as int, b3 as int, false, true)
                    == (check2 || check6)
            );
            assert(
                placement_with_orientations(a1 as int, b1 as int, a2 as int, b2 as int, a3 as int, b3 as int, true, false)
                    == (check3 || check7)
            );
            assert(
                placement_with_orientations(a1 as int, b1 as int, a2 as int, b2 as int, a3 as int, b3 as int, true, true)
                    == (check4 || check8)
            );
            assert(can_place_paintings_cases(a1 as int, b1 as int, a2 as int, b2 as int, a3 as int, b3 as int) == result);
            assert(result == can_place_paintings_spec(a1 as int, b1 as int, a2 as int, b2 as int, a3 as int, b3 as int));
        }
        result
    }
}

}
