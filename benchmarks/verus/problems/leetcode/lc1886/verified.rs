use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn matches_rot0(mat: Seq<Vec<i32>>, target: Seq<Vec<i32>>, n: int) -> bool {
        forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==>
            mat[i]@[j] == target[i]@[j]
    }

    pub open spec fn matches_rot90(mat: Seq<Vec<i32>>, target: Seq<Vec<i32>>, n: int) -> bool {
        forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==>
            mat[i]@[j] == target[j]@[n - 1 - i]
    }

    pub open spec fn matches_rot180(mat: Seq<Vec<i32>>, target: Seq<Vec<i32>>, n: int) -> bool {
        forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==>
            mat[i]@[j] == target[n - 1 - i]@[n - 1 - j]
    }

    pub open spec fn matches_rot270(mat: Seq<Vec<i32>>, target: Seq<Vec<i32>>, n: int) -> bool {
        forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==>
            mat[i]@[j] == target[n - 1 - j]@[i]
    }

    pub open spec fn partial_rot0(mat: Seq<Vec<i32>>, target: Seq<Vec<i32>>, n: int, ri: int, rj: int) -> bool {
        forall |a: int, b: int| 0 <= a < n && 0 <= b < n
            && (a < ri || (a == ri && b < rj)) ==>
            mat[a]@[b] == target[a]@[b]
    }

    pub open spec fn partial_rot90(mat: Seq<Vec<i32>>, target: Seq<Vec<i32>>, n: int, ri: int, rj: int) -> bool {
        forall |a: int, b: int| 0 <= a < n && 0 <= b < n
            && (a < ri || (a == ri && b < rj)) ==>
            mat[a]@[b] == target[b]@[n - 1 - a]
    }

    pub open spec fn partial_rot180(mat: Seq<Vec<i32>>, target: Seq<Vec<i32>>, n: int, ri: int, rj: int) -> bool {
        forall |a: int, b: int| 0 <= a < n && 0 <= b < n
            && (a < ri || (a == ri && b < rj)) ==>
            mat[a]@[b] == target[n - 1 - a]@[n - 1 - b]
    }

    pub open spec fn partial_rot270(mat: Seq<Vec<i32>>, target: Seq<Vec<i32>>, n: int, ri: int, rj: int) -> bool {
        forall |a: int, b: int| 0 <= a < n && 0 <= b < n
            && (a < ri || (a == ri && b < rj)) ==>
            mat[a]@[b] == target[n - 1 - b]@[a]
    }

    pub fn find_rotation(mat: Vec<Vec<i32>>, target: Vec<Vec<i32>>) -> (result: bool)
        requires
            1 <= mat@.len() <= 10,
            mat@.len() == target@.len(),
            forall |i: int| 0 <= i < mat@.len() ==> (#[trigger] mat@[i])@.len() == mat@.len(),
            forall |i: int| 0 <= i < target@.len() ==> (#[trigger] target@[i])@.len() == target@.len(),
            forall |i: int, j: int| 0 <= i < mat@.len() && 0 <= j < mat@.len() ==>
                (mat@[i]@[j] == 0 || mat@[i]@[j] == 1),
            forall |i: int, j: int| 0 <= i < target@.len() && 0 <= j < target@.len() ==>
                (target@[i]@[j] == 0 || target@[i]@[j] == 1),
        ensures
            result == (
                Self::matches_rot0(mat@, target@, mat@.len() as int) ||
                Self::matches_rot90(mat@, target@, mat@.len() as int) ||
                Self::matches_rot180(mat@, target@, mat@.len() as int) ||
                Self::matches_rot270(mat@, target@, mat@.len() as int)
            ),
    {
        let n = mat.len();
        let mut r0 = true;
        let mut r90 = true;
        let mut r180 = true;
        let mut r270 = true;
        let mut i: usize = 0;
        while i < n
            invariant
                n == mat@.len(),
                n == target@.len(),
                1 <= n <= 10,
                forall |k: int| 0 <= k < n as int ==> (#[trigger] mat@[k])@.len() == n as int,
                forall |k: int| 0 <= k < n as int ==> (#[trigger] target@[k])@.len() == n as int,
                0 <= i <= n,
                r0 == Self::partial_rot0(mat@, target@, n as int, i as int, 0),
                r90 == Self::partial_rot90(mat@, target@, n as int, i as int, 0),
                r180 == Self::partial_rot180(mat@, target@, n as int, i as int, 0),
                r270 == Self::partial_rot270(mat@, target@, n as int, i as int, 0),
            decreases n - i,
        {
            let mut j: usize = 0;
            while j < n
                invariant
                    n == mat@.len(),
                    n == target@.len(),
                    1 <= n <= 10,
                    forall |k: int| 0 <= k < n as int ==> (#[trigger] mat@[k])@.len() == n as int,
                    forall |k: int| 0 <= k < n as int ==> (#[trigger] target@[k])@.len() == n as int,
                    0 <= i < n,
                    0 <= j <= n,
                    r0 == Self::partial_rot0(mat@, target@, n as int, i as int, j as int),
                    r90 == Self::partial_rot90(mat@, target@, n as int, i as int, j as int),
                    r180 == Self::partial_rot180(mat@, target@, n as int, i as int, j as int),
                    r270 == Self::partial_rot270(mat@, target@, n as int, i as int, j as int),
                decreases n - j,
            {
                if mat[i][j] != target[i][j] {
                    r0 = false;
                }
                if mat[i][j] != target[j][n - 1 - i] {
                    r90 = false;
                }
                if mat[i][j] != target[n - 1 - i][n - 1 - j] {
                    r180 = false;
                }
                if mat[i][j] != target[n - 1 - j][i] {
                    r270 = false;
                }
                j += 1;
            }
            i += 1;
        }
        r0 || r90 || r180 || r270
    }
}

}
