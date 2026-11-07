use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn total_len(arrays: Seq<Vec<i32>>) -> int
        decreases arrays.len(),
    {
        if arrays.len() == 0 {
            0
        } else {
            arrays[0].len() + Self::total_len(arrays.drop_first())
        }
    }

    pub open spec fn abs_diff(x: int, y: int) -> int {
        if x >= y { x - y } else { y - x }
    }

    pub fn max_distance(arrays: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= arrays.len() <= 100_000,
            forall |a: int| 0 <= a < arrays.len() ==> 1 <= #[trigger] arrays[a].len() <= 500,
            Self::total_len(arrays@) <= 100_000,
            forall |a: int, i: int| 0 <= a < arrays.len() && 0 <= i < arrays[a].len() ==>
                -10_000 <= #[trigger] arrays[a][i] <= 10_000,
            forall |a: int, i: int, j: int|
                0 <= a < arrays.len() && 0 <= i < j < arrays[a].len() ==>
                arrays[a][i] <= arrays[a][j],
        ensures
            result >= 0,
            exists |a: int, b: int, i: int, j: int|
                0 <= a < arrays.len()
                && 0 <= b < arrays.len()
                && a != b
                && 0 <= i < arrays[a].len()
                && 0 <= j < arrays[b].len()
                && #[trigger] Self::abs_diff(arrays[a][i] as int, arrays[b][j] as int) == result as int,
            forall |a: int, b: int, i: int, j: int|
                0 <= a < arrays.len()
                && 0 <= b < arrays.len()
                && a != b
                && 0 <= i < arrays[a].len()
                && 0 <= j < arrays[b].len()
                ==> #[trigger] Self::abs_diff(arrays[a][i] as int, arrays[b][j] as int) <= result as int,
    {
        let ghost s = arrays@;
        let mut min_val = arrays[0][0];
        let mut max_val = arrays[0][arrays[0].len() - 1];
        let mut result = 0i32;
        let mut i: usize = 1;
        let ghost mut min_idx: int = 0;
        let ghost mut max_idx: int = 0;
        let ghost mut best_a: int = 0;
        let ghost mut best_b: int = 0;
        let ghost mut best_i: int = 0;
        let ghost mut best_j: int = 0;

        while i < arrays.len()
            invariant
                s == arrays@,
                2 <= arrays.len() <= 100_000,
                1 <= i <= arrays.len(),
                forall |a: int| 0 <= a < arrays.len() ==> 1 <= #[trigger] arrays[a].len() <= 500,
                Self::total_len(s) <= 100_000,
                forall |a: int, j: int| 0 <= a < arrays.len() && 0 <= j < arrays[a].len() ==>
                    -10_000 <= #[trigger] arrays[a][j] <= 10_000,
                forall |a: int, x: int, y: int|
                    0 <= a < arrays.len() && 0 <= x < y < arrays[a].len() ==>
                    arrays[a][x] <= arrays[a][y],
                0 <= min_idx < i,
                min_val == s[min_idx][0],
                forall |a: int| 0 <= a < i ==> min_val <= #[trigger] s[a][0],
                0 <= max_idx < i,
                max_val == s[max_idx][s[max_idx].len() - 1],
                forall |a: int| 0 <= a < i ==> max_val >= #[trigger] s[a][s[a].len() - 1],
                result >= 0,
                i >= 2 ==> (
                    0 <= best_a < i
                    && 0 <= best_b < i
                    && best_a != best_b
                    && 0 <= best_i < s[best_a].len()
                    && 0 <= best_j < s[best_b].len()
                    && Self::abs_diff(s[best_a][best_i] as int, s[best_b][best_j] as int) == result as int
                ),
                forall |a: int, b: int, x: int, y: int|
                    0 <= a < i
                    && 0 <= b < i
                    && a != b
                    && 0 <= x < s[a].len()
                    && 0 <= y < s[b].len()
                    ==> #[trigger] Self::abs_diff(s[a][x] as int, s[b][y] as int) <= result as int,
            decreases arrays.len() - i,
        {
            let ghost cur = i as int;
            let curr_len = arrays[i].len();
            let curr_last = curr_len - 1;
            let curr_min = arrays[i][0];
            let curr_max = arrays[i][curr_last];
            let old_min_val = min_val;
            let old_max_val = max_val;
            let old_result = result;
            let ghost old_min_idx = min_idx;
            let ghost old_max_idx = max_idx;

            let mut candidate = curr_max - old_min_val;
            let other = old_max_val - curr_min;
            if other > candidate {
                candidate = other;
            }
            if i == 1 || candidate > result {
                result = candidate;
                proof {
                    if curr_max - old_min_val >= old_max_val - curr_min {
                        best_a = old_min_idx;
                        best_b = cur;
                        best_i = 0;
                        best_j = curr_last as int;
                        assert(curr_max - old_min_val == candidate);
                        assert(candidate >= 0);
                        assert(Self::abs_diff(s[best_a][best_i] as int, s[best_b][best_j] as int) == result as int);
                    } else {
                        best_a = old_max_idx;
                        best_b = cur;
                        best_i = s[best_a].len() - 1;
                        best_j = 0;
                        assert(old_max_val - curr_min == candidate);
                        assert(candidate >= 0);
                        assert(Self::abs_diff(s[best_a][best_i] as int, s[best_b][best_j] as int) == result as int);
                    }
                }
            }
            proof {
                assert(candidate <= result);
            }

            if curr_min < min_val {
                min_val = curr_min;
                proof {
                    min_idx = cur;
                }
            }
            if curr_max > max_val {
                max_val = curr_max;
                proof {
                    max_idx = cur;
                }
            }

            proof {
                assert forall |a: int| 0 <= a < cur + 1 implies min_val <= #[trigger] s[a][0] by {
                    if a < cur {
                        if curr_min < old_min_val {
                            assert(min_val == curr_min);
                            assert(0 <= a < cur);
                            assert(old_min_val <= s[a][0]);
                        } else {
                            assert(min_val == old_min_val);
                        }
                    } else {
                        assert(a == cur);
                        if curr_min < old_min_val {
                            assert(min_val == curr_min);
                        } else {
                            assert(min_val == old_min_val);
                            assert(curr_min >= old_min_val);
                        }
                    }
                }
                assert forall |a: int| 0 <= a < cur + 1 implies max_val >= #[trigger] s[a][s[a].len() - 1] by {
                    if a < cur {
                        if curr_max > old_max_val {
                            assert(max_val == curr_max);
                            assert(old_max_val >= s[a][s[a].len() - 1]);
                        } else {
                            assert(max_val == old_max_val);
                        }
                    } else {
                        assert(a == cur);
                        if curr_max > old_max_val {
                            assert(max_val == curr_max);
                        } else {
                            assert(max_val == old_max_val);
                            assert(curr_max <= old_max_val);
                        }
                    }
                }
                assert forall |a: int, b: int, x: int, y: int|
                    0 <= a < cur + 1
                    && 0 <= b < cur + 1
                    && a != b
                    && 0 <= x < s[a].len()
                    && 0 <= y < s[b].len()
                    implies #[trigger] Self::abs_diff(s[a][x] as int, s[b][y] as int) <= result as int by {
                    if a < cur && b < cur {
                    } else {
                        let old_a = if a == cur { b } else { a };
                        let old_x = if a == cur { y } else { x };
                        let cur_y = if a == cur { x } else { y };
                        assert(0 <= old_a < cur);
                        assert(0 <= old_x < s[old_a].len());
                        assert(0 <= cur_y < s[cur].len());
                        if old_x > 0 {
                            assert(s[old_a][0] <= s[old_a][old_x]);
                        }
                        if old_x < s[old_a].len() - 1 {
                            assert(s[old_a][old_x] <= s[old_a][s[old_a].len() - 1]);
                        }
                        if cur_y > 0 {
                            assert(s[cur][0] <= s[cur][cur_y]);
                        }
                        if cur_y < s[cur].len() - 1 {
                            assert(s[cur][cur_y] <= s[cur][s[cur].len() - 1]);
                        }
                        if s[old_a][old_x] as int >= s[cur][cur_y] as int {
                            assert(Self::abs_diff(s[old_a][old_x] as int, s[cur][cur_y] as int)
                                == s[old_a][old_x] as int - s[cur][cur_y] as int);
                            assert(s[old_a][old_x] as int - s[cur][cur_y] as int
                                <= s[old_a][s[old_a].len() - 1] as int - s[cur][0] as int);
                            assert(s[old_a][s[old_a].len() - 1] as int <= old_max_val as int);
                            assert(s[cur][0] as int == curr_min as int);
                            assert(old_max_val as int - curr_min as int == other as int);
                            assert(Self::abs_diff(s[old_a][old_x] as int, s[cur][cur_y] as int) <= other as int);
                        } else {
                            assert(Self::abs_diff(s[old_a][old_x] as int, s[cur][cur_y] as int)
                                == s[cur][cur_y] as int - s[old_a][old_x] as int);
                            assert(s[cur][cur_y] as int - s[old_a][old_x] as int
                                <= s[cur][s[cur].len() - 1] as int - s[old_a][0] as int);
                            assert(s[cur][s[cur].len() - 1] as int == curr_max as int);
                            assert(s[old_a][0] as int >= old_min_val as int);
                            assert(curr_max as int - old_min_val as int == (curr_max - old_min_val) as int);
                            assert(Self::abs_diff(s[old_a][old_x] as int, s[cur][cur_y] as int)
                                <= (curr_max - old_min_val) as int);
                        }
                    }
                }
                if cur + 1 >= 2 && !(i == 1 || candidate > old_result) {
                    assert(0 <= best_a < cur);
                    assert(0 <= best_b < cur);
                    assert(0 <= best_i < s[best_a].len());
                    assert(0 <= best_j < s[best_b].len());
                    assert(Self::abs_diff(s[best_a][best_i] as int, s[best_b][best_j] as int) == result as int);
                }
            }

            i += 1;
        }

        proof {
            assert(0 <= best_a < arrays.len());
            assert(0 <= best_b < arrays.len());
            assert(best_a != best_b);
            assert(0 <= best_i < s[best_a].len());
            assert(0 <= best_j < s[best_b].len());
            assert(Self::abs_diff(s[best_a][best_i] as int, s[best_b][best_j] as int) == result as int);
            assert forall |a: int, b: int, x: int, y: int|
                0 <= a < arrays.len()
                && 0 <= b < arrays.len()
                && a != b
                && 0 <= x < s[a].len()
                && 0 <= y < s[b].len()
                implies #[trigger] Self::abs_diff(s[a][x] as int, s[b][y] as int) <= result as int by {
            }
        }
        result
    }
}

}
