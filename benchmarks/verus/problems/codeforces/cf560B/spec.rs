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
    }
}

}
