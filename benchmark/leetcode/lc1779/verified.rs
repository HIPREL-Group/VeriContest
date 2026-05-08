use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs(val: int) -> int {
    if val < 0 { -val } else { val }
}

pub open spec fn dist(x: int, y: int, x1: int, y1: int) -> int {
    abs(x - x1) + abs(y - y1)
}

pub open spec fn valid_pt(p: Seq<i32>) -> bool {
    p.len() == 2 && 1 <= p[0] && p[0] <= 10000 && 1 <= p[1] && p[1] <= 10000
}

impl Solution {
    pub fn nearest_valid_point(x: i32, y: i32, points: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= points.len() <= 10000,
            forall |i: int| #![trigger valid_pt(points[i]@)] 0 <= i < points.len() ==> valid_pt(points[i]@),
            1 <= x <= 10000,
            1 <= y <= 10000,
        ensures
            result >= -1,
            result < points.len(),
            result == -1 ==> forall |i: int| 0 <= i < points.len() && valid_pt(points[i]@) ==> (#[trigger] points[i][0] != x && #[trigger] points[i][1] != y),
            result != -1 ==> (
                valid_pt(points[result as int]@) && (#[trigger] points[result as int][0] == x || #[trigger] points[result as int][1] == y)
            ) &&
            forall |i: int| 0 <= i < points.len() && valid_pt(points[i]@) && (#[trigger] points[i][0] == x || #[trigger] points[i][1] == y) ==>
                dist(x as int, y as int, #[trigger] points[i][0] as int, #[trigger] points[i][1] as int) > dist(x as int, y as int, points[result as int][0] as int, points[result as int][1] as int) ||
                (dist(x as int, y as int, points[i][0] as int, points[i][1] as int) == dist(x as int, y as int, points[result as int][0] as int, points[result as int][1] as int) && result <= i),
    {
        let n: usize = points.len();
        let mut min_dist: i32 = 30000;
        let mut min_idx: i32 = -1;
        let mut i: usize = 0;
        
        while i < n
            invariant
                n == points.len(),
                1 <= n <= 10000,
                0 <= i <= n,
                1 <= x <= 10000 && 1 <= y <= 10000,
                forall |k: int| #![auto] 0 <= k < n ==> valid_pt(points[k]@),
                min_idx >= -1,
                min_idx < i,
                0 <= min_dist <= 30000,
                min_idx == -1 <==> min_dist == 30000,
                min_idx == -1 ==> forall |k: int| 0 <= k < i && valid_pt(points[k]@) ==> (#[trigger] points[k][0] != x && #[trigger] points[k][1] != y),
                min_idx != -1 ==> (
                    valid_pt(points[min_idx as int]@) && (#[trigger] points[min_idx as int][0] == x || #[trigger] points[min_idx as int][1] == y)
                ) && 
                min_dist == dist(x as int, y as int, #[trigger] points[min_idx as int][0] as int, #[trigger] points[min_idx as int][1] as int),
                forall |k: int| 0 <= k < i && valid_pt(points[k]@) && (#[trigger] points[k][0] == x || #[trigger] points[k][1] == y) ==>
                    min_dist < dist(x as int, y as int, #[trigger] points[k][0] as int, #[trigger] points[k][1] as int) ||
                    (min_dist == dist(x as int, y as int, points[k][0] as int, points[k][1] as int) && min_idx <= k),
            decreases n - i,
        {
            let px = points[i][0];
            let py = points[i][1];
            
            if px == x || py == y {
                let dx = if px > x { px - x } else { x - px };
                let dy = if py > y { py - y } else { y - py };
                let d = dx + dy;
                
                assert(d == dist(x as int, y as int, px as int, py as int));
                assert(d <= 20000); 
                
                if d < min_dist {
                    min_dist = d;
                    min_idx = i as i32;
                }
            } else {
                assert(points[i as int][0] != x);
                assert(points[i as int][1] != y);
            }
            i = i + 1;
        }
        
        if min_idx == -1 {
            assert forall |k: int| 0 <= k < points.len() && valid_pt(points[k]@) implies (#[trigger] points[k][0] != x && #[trigger] points[k][1] != y) by {
            };
        }
        
        min_idx
    }
}

}
