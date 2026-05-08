use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min(a: int, b: int) -> int {
        if a < b {
            a
        } else {
            b
        }
    }

    pub fn max_area(height: Vec<i32>) -> (result: i32)
        requires
            2 <= height.len() <= 100_000,
            forall|i: int| 0 <= i < height.len() ==> 0 <= #[trigger] height[i] <= 10_000,
        ensures
            forall|i: int, j: int|
                0 <= i < j < height.len() ==> result as int >= (j - i) * Solution::min(
                    height[i] as int,
                    height[j] as int,
                ),
            exists|i: int, j: int|
                0 <= i < j < height.len() && result as int == (j - i) * Solution::min(
                    height[i] as int,
                    height[j] as int,
                ),
    {
        let n = height.len();
        let mut left: usize = 0;
        let mut right: usize = n - 1;

        let init_width = (right - left) as i32;
        let init_h = if height[left] < height[right] {
            height[left]
        } else {
            height[right]
        };

        assert(init_width * init_h <= 1_000_000_000) by (nonlinear_arith)
            requires
                0 <= init_width,
                init_width <= 100_000,
                0 <= init_h,
                init_h <= 10_000,
        {}

        let mut max_area: i32 = init_width * init_h;
        let mut best_i: usize = left;
        let mut best_j: usize = right;

        assert(max_area as int == (best_j as int - best_i as int) * Solution::min(
            height[best_i as int] as int,
            height[best_j as int] as int,
        ));

        assert(0 <= max_area <= 1_000_000_000) by (nonlinear_arith)
            requires
                0 <= init_width,
                init_width <= 100_000,
                0 <= init_h,
                init_h <= 10_000,
                max_area == init_width * init_h,
        {}

        while left < right
            invariant
                n == height.len(),
                2 <= n <= 100_000,
                forall|k: int| 0 <= k < height.len() ==> 0 <= #[trigger] height[k] <= 10_000,
                0 <= left < n,
                0 <= right < n,
                left <= right,
                0 <= max_area <= 1_000_000_000,
                0 <= best_i < best_j < n,
                max_area as int == (best_j as int - best_i as int) * Solution::min(
                    height[best_i as int] as int,
                    height[best_j as int] as int,
                ),
                forall|ii: int, jj: int|
                    0 <= ii < jj < n && (ii < left as int || jj > right as int) ==> max_area as int
                        >= (jj - ii) * Solution::min(height[ii] as int, height[jj] as int),
            decreases right - left,
        {
            let cur_left = left;
            let cur_right = right;
            let ghost cur_left_i: int = cur_left as int;
            let ghost cur_right_i: int = cur_right as int;

            let width = (cur_right - cur_left) as i32;
            let h = if height[cur_left] < height[cur_right] {
                height[cur_left]
            } else {
                height[cur_right]
            };

            assert(width * h <= 1_000_000_000) by (nonlinear_arith)
                requires
                    0 <= width,
                    width <= 100_000,
                    0 <= h,
                    h <= 10_000,
            {}

            let area = width * h;
            assert(area as int == (cur_right_i - cur_left_i) * Solution::min(
                height[cur_left_i] as int,
                height[cur_right_i] as int,
            ));

            if area > max_area {
                max_area = area;
                best_i = cur_left;
                best_j = cur_right;
                assert(max_area as int == (best_j as int - best_i as int) * Solution::min(
                    height[best_i as int] as int,
                    height[best_j as int] as int,
                ));
            }

            assert(max_area as int >= area as int);

            if height[cur_left] <= height[cur_right] {
                assert forall|jj: int|
                    cur_left_i < jj && jj <= cur_right_i implies max_area as int >= (jj - cur_left_i)
                        * Solution::min(
                        height[cur_left_i] as int,
                        height[jj] as int,
                    ) by {
                    assert(0 <= jj - cur_left_i <= cur_right_i - cur_left_i);
                    assert(
                        0 <= Solution::min(height[cur_left_i] as int, height[jj] as int)
                            <= height[cur_left_i] as int
                    );
                    assert(
                        Solution::min(height[cur_left_i] as int, height[cur_right_i] as int)
                            == height[cur_left_i] as int
                    );
                    assert(Solution::min(height[cur_left_i] as int, height[jj] as int) <= height[cur_left_i] as int);
                    assert((jj - cur_left_i) * Solution::min(
                        height[cur_left_i] as int,
                        height[jj] as int,
                    ) <= (jj - cur_left_i) * (height[cur_left_i] as int)) by (nonlinear_arith)
                        requires
                            0 <= jj - cur_left_i,
                            Solution::min(height[cur_left_i] as int, height[jj] as int)
                                <= height[cur_left_i] as int,
                    {};
                    assert((jj - cur_left_i) * (height[cur_left_i] as int) <= (cur_right_i
                        - cur_left_i) * (height[cur_left_i] as int)) by (nonlinear_arith)
                        requires
                            0 <= height[cur_left_i] as int,
                            0 <= jj - cur_left_i <= cur_right_i - cur_left_i,
                    {};
                    assert((cur_right_i - cur_left_i) * (height[cur_left_i] as int) == area as int);
                    assert((jj - cur_left_i) * Solution::min(
                        height[cur_left_i] as int,
                        height[jj] as int,
                    ) <= area as int) by (nonlinear_arith)
                        requires
                            (jj - cur_left_i) * Solution::min(
                                height[cur_left_i] as int,
                                height[jj] as int,
                            ) <= (jj - cur_left_i) * (height[cur_left_i] as int),
                            (jj - cur_left_i) * (height[cur_left_i] as int)
                                <= (cur_right_i - cur_left_i) * (height[cur_left_i] as int),
                            (cur_right_i - cur_left_i) * (height[cur_left_i] as int) == area as int,
                    {};
                }

                left += 1;

                assert forall|ii: int, jj: int|
                    0 <= ii < jj < n && (ii < left as int || jj > right as int) implies max_area
                        as int >= (jj - ii) * Solution::min(height[ii] as int, height[jj] as int) by {
                    if ii < cur_left_i || jj > cur_right_i {
                        assert(max_area as int >= (jj - ii) * Solution::min(
                            height[ii] as int,
                            height[jj] as int,
                        ));
                    } else {
                        assert(ii < left as int);
                        assert(jj <= cur_right_i);
                        assert(ii == cur_left_i);
                        assert(cur_left_i < jj && jj <= cur_right_i);
                        assert(max_area as int >= (jj - ii) * Solution::min(
                            height[ii] as int,
                            height[jj] as int,
                        ));
                    }
                }
            } else {
                assert forall|ii: int|
                    cur_left_i <= ii && ii < cur_right_i implies max_area as int >= (cur_right_i - ii)
                        * Solution::min(height[ii] as int, height[cur_right_i] as int) by {
                    assert(0 <= cur_right_i - ii <= cur_right_i - cur_left_i);
                    assert(
                        0 <= Solution::min(height[ii] as int, height[cur_right_i] as int)
                            <= height[cur_right_i] as int
                    );
                    assert(
                        Solution::min(height[cur_left_i] as int, height[cur_right_i] as int)
                            == height[cur_right_i] as int
                    );
                    assert(Solution::min(height[ii] as int, height[cur_right_i] as int) <= height[cur_right_i] as int);
                    assert((cur_right_i - ii) * Solution::min(
                        height[ii] as int,
                        height[cur_right_i] as int,
                    ) <= (cur_right_i - ii) * (height[cur_right_i] as int)) by (nonlinear_arith)
                        requires
                            0 <= cur_right_i - ii,
                            Solution::min(height[ii] as int, height[cur_right_i] as int)
                                <= height[cur_right_i] as int,
                    {};
                    assert((cur_right_i - ii) * (height[cur_right_i] as int) <= (cur_right_i
                        - cur_left_i) * (height[cur_right_i] as int)) by (nonlinear_arith)
                        requires
                            0 <= height[cur_right_i] as int,
                            0 <= cur_right_i - ii <= cur_right_i - cur_left_i,
                    {};
                    assert((cur_right_i - cur_left_i) * (height[cur_right_i] as int) == area as int);
                    assert((cur_right_i - ii) * Solution::min(
                        height[ii] as int,
                        height[cur_right_i] as int,
                    ) <= area as int) by (nonlinear_arith)
                        requires
                            (cur_right_i - ii) * Solution::min(
                                height[ii] as int,
                                height[cur_right_i] as int,
                            ) <= (cur_right_i - ii) * (height[cur_right_i] as int),
                            (cur_right_i - ii) * (height[cur_right_i] as int)
                                <= (cur_right_i - cur_left_i) * (height[cur_right_i] as int),
                            (cur_right_i - cur_left_i) * (height[cur_right_i] as int) == area as int,
                    {};
                }

                right -= 1;

                assert forall|ii: int, jj: int|
                    0 <= ii < jj < n && (ii < left as int || jj > right as int) implies max_area
                        as int >= (jj - ii) * Solution::min(height[ii] as int, height[jj] as int) by {
                    if ii < cur_left_i || jj > cur_right_i {
                        assert(max_area as int >= (jj - ii) * Solution::min(
                            height[ii] as int,
                            height[jj] as int,
                        ));
                    } else {
                        assert(jj > right as int);
                        assert(ii >= cur_left_i);
                        assert(jj == cur_right_i);
                        assert(cur_left_i <= ii && ii < cur_right_i);
                        assert(max_area as int >= (jj - ii) * Solution::min(
                            height[ii] as int,
                            height[jj] as int,
                        ));
                    }
                }
            }
        }

        assert(forall|i: int, j: int|
            0 <= i < j < n ==> max_area as int >= (j - i) * Solution::min(
                height[i] as int,
                height[j] as int,
            )) by {
            assert(left >= right);
            assert forall|i: int, j: int| 0 <= i < j < n implies max_area as int >= (j - i)
                * Solution::min(height[i] as int, height[j] as int) by {
                if !(i < left as int || j > right as int) {
                    assert(i >= left as int);
                    assert(j <= right as int);
                    assert(left as int >= right as int);
                    assert(false) by (nonlinear_arith)
                        requires
                            i >= left as int,
                            j <= right as int,
                            i < j,
                            left as int >= right as int,
                    {};
                }
                assert(i < left as int || j > right as int);
                assert(max_area as int >= (j - i) * Solution::min(
                    height[i] as int,
                    height[j] as int,
                ));
            }
        }

        assert(exists|i: int, j: int|
            0 <= i < j < n && max_area as int == (j - i) * Solution::min(
                height[i] as int,
                height[j] as int,
            )) by {
            assert(0 <= best_i < best_j < n);
            assert(max_area as int == (best_j as int - best_i as int) * Solution::min(
                height[best_i as int] as int,
                height[best_j as int] as int,
            ));
        }

        max_area
    }
}

} 
