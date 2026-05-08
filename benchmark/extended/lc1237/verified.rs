use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub struct CustomFunction {
    pub values: Vec<Vec<i32>>,
}

impl CustomFunction {
    pub fn f(&self, x: i32, y: i32) -> (result: i32)
        requires
            0 <= x < self.values@.len(),
            0 <= y < self.values@[x as int]@.len(),
        ensures
            result == self.values@[x as int]@[y as int],
    {
        self.values[x as usize][y as usize]
    }
}

pub open spec fn grid_val(f: Seq<Vec<i32>>, x: int, y: int) -> i32 {
    f[x]@[y]
}

pub open spec fn is_monotonic_grid(f: Seq<Vec<i32>>) -> bool {
    &&& f.len() >= 1001
    &&& forall |x: int| 0 <= x <= 1000 ==> (#[trigger] f[x])@.len() >= 1001
    &&& forall |x: int, y: int| 1 <= x < 1000 && 1 <= y <= 1000 ==>
        (#[trigger] grid_val(f, x, y)) < grid_val(f, x + 1, y)
    &&& forall |x: int, y: int| 1 <= x <= 1000 && 1 <= y < 1000 ==>
        (#[trigger] grid_val(f, x, y)) < grid_val(f, x, y + 1)
}

proof fn monotonic_x(f: Seq<Vec<i32>>, x1: int, x2: int, y: int)
    requires
        is_monotonic_grid(f),
        1 <= x1,
        x1 < x2,
        x2 <= 1000,
        1 <= y <= 1000,
    ensures
        grid_val(f, x1, y) < grid_val(f, x2, y),
    decreases x2 - x1,
{
    if x1 + 1 < x2 {
        monotonic_x(f, x1 + 1, x2, y);
    }
}

proof fn monotonic_y(f: Seq<Vec<i32>>, x: int, y1: int, y2: int)
    requires
        is_monotonic_grid(f),
        1 <= x <= 1000,
        1 <= y1,
        y1 < y2,
        y2 <= 1000,
    ensures
        grid_val(f, x, y1) < grid_val(f, x, y2),
    decreases y2 - y1,
{
    if y1 + 1 < y2 {
        monotonic_y(f, x, y1 + 1, y2);
    }
}

impl Solution {
    pub fn find_solution(customfunction: &CustomFunction, z: i32) -> (result: Vec<Vec<i32>>)
        requires
            is_monotonic_grid(customfunction.values@),
            1 <= z <= 100,
        ensures
            forall |i: int| 0 <= i < result@.len() ==>
                (#[trigger] result@[i])@.len() == 2,
            forall |i: int| 0 <= i < result@.len() ==>
                1 <= (#[trigger] result@[i])@[0] <= 1000
                && 1 <= result@[i]@[1] <= 1000
                && grid_val(customfunction.values@, result@[i]@[0] as int, result@[i]@[1] as int) == z,
            forall |a: int, b: int| 1 <= a <= 1000 && 1 <= b <= 1000
                && grid_val(customfunction.values@, a, b) == z ==>
                exists |i: int| #![auto] 0 <= i < result@.len()
                    && result@[i]@[0] == a as i32
                    && result@[i]@[1] == b as i32,
    {
        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut x: usize = 1;
        let mut y: usize = 1000;
        while x <= 1000 && y >= 1
            invariant
                is_monotonic_grid(customfunction.values@),
                1 <= z <= 100,
                1 <= x <= 1001,
                0 <= y <= 1000,
                forall |i: int| 0 <= i < result@.len() ==>
                    (#[trigger] result@[i])@.len() == 2,
                forall |i: int| 0 <= i < result@.len() ==>
                    1 <= (#[trigger] result@[i])@[0] <= 1000
                    && 1 <= result@[i]@[1] <= 1000
                    && grid_val(customfunction.values@, result@[i]@[0] as int, result@[i]@[1] as int) == z,
                forall |a: int, b: int| 1 <= a <= 1000 && 1 <= b <= 1000
                    && grid_val(customfunction.values@, a, b) == z
                    && (a < x as int || b > y as int) ==>
                    exists |i: int| #![auto] 0 <= i < result@.len()
                        && result@[i]@[0] == a as i32
                        && result@[i]@[1] == b as i32,
            decreases 1001 - x + y,
        {
            let val = customfunction.f(x as i32, y as i32);
            if val == z {
                let ghost old_result = result@;
                let ghost old_len = result@.len() as int;
                let ghost old_x = x as int;
                let ghost old_y = y as int;
                let mut pair: Vec<i32> = Vec::new();
                pair.push(x as i32);
                pair.push(y as i32);
                let ghost pair_val = pair;
                result.push(pair);

                proof {
                    assert(result@.len() == old_len + 1);
                    assert(result@ =~= old_result.push(pair_val));

                    assert forall |i: int| 0 <= i < result@.len()
                    implies (#[trigger] result@[i])@.len() == 2 by {
                        if i < old_len {
                            assert(old_result[i]@.len() == 2);
                        } else {
                            assert(pair_val@.len() == 2);
                        }
                    };

                    assert forall |i: int| 0 <= i < result@.len()
                    implies
                        1 <= (#[trigger] result@[i])@[0] <= 1000
                        && 1 <= result@[i]@[1] <= 1000
                        && grid_val(customfunction.values@, result@[i]@[0] as int, result@[i]@[1] as int) == z
                    by {
                        if i < old_len {
                            assert(old_result[i]@[0] == result@[i]@[0]);
                            assert(old_result[i]@[1] == result@[i]@[1]);
                        } else {
                            assert(result@[old_len]@[0] == old_x as i32);
                            assert(result@[old_len]@[1] == old_y as i32);
                        }
                    };

                    assert forall |a: int, b: int|
                        1 <= a <= 1000 && 1 <= b <= 1000
                        && grid_val(customfunction.values@, a, b) == z
                        && (a < old_x + 1 || b > old_y - 1)
                    implies
                        exists |i: int| #![auto] 0 <= i < result@.len()
                            && result@[i]@[0] == a as i32
                            && result@[i]@[1] == b as i32
                    by {
                        if a < old_x || b > old_y {
                            let wit = choose |i: int| #![auto] 0 <= i < old_len
                                && old_result[i]@[0] == a as i32
                                && old_result[i]@[1] == b as i32;
                            assert(result@[wit]@[0] == a as i32);
                            assert(result@[wit]@[1] == b as i32);
                        } else if a > old_x {
                            assert(b == old_y);
                            monotonic_x(customfunction.values@, old_x, a, old_y);
                        } else if b < old_y {
                            assert(a == old_x);
                            monotonic_y(customfunction.values@, old_x, b, old_y);
                        } else {
                            assert(a == old_x && b == old_y);
                            assert(result@[old_len]@[0] == a as i32);
                            assert(result@[old_len]@[1] == b as i32);
                        }
                    };
                }

                x = x + 1;
                y = y - 1;
            } else if val < z {
                proof {
                    assert forall |a: int, b: int|
                        1 <= a <= 1000 && 1 <= b <= 1000
                        && grid_val(customfunction.values@, a, b) == z
                        && (a < x as int + 1 || b > y as int)
                    implies
                        exists |i: int| #![auto] 0 <= i < result@.len()
                            && result@[i]@[0] == a as i32
                            && result@[i]@[1] == b as i32
                    by {
                        if a < x as int || b > y as int {
                        } else {
                            assert(a == x as int);
                            if b < y as int {
                                monotonic_y(customfunction.values@, a, b, y as int);
                            }
                        }
                    };
                }
                x = x + 1;
            } else {
                proof {
                    assert forall |a: int, b: int|
                        1 <= a <= 1000 && 1 <= b <= 1000
                        && grid_val(customfunction.values@, a, b) == z
                        && (a < x as int || b > y as int - 1)
                    implies
                        exists |i: int| #![auto] 0 <= i < result@.len()
                            && result@[i]@[0] == a as i32
                            && result@[i]@[1] == b as i32
                    by {
                        if a < x as int || b > y as int {
                        } else {
                            assert(b == y as int);
                            if a > x as int {
                                monotonic_x(customfunction.values@, x as int, a, b);
                            }
                        }
                    };
                }
                y = y - 1;
            }
        }
        result
    }
}

}
