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
    }
}

}
