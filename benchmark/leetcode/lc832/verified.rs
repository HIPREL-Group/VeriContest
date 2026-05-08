use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn flip_and_invert_image(image: Vec<Vec<i32>>) -> (res: Vec<Vec<i32>>)
        requires
            1 <= image.len() <= 20,
            forall |i: int| 0 <= i < image.len() ==> #[trigger] image[i].len() == image.len(),
            forall |i: int, j: int| 0 <= i < image.len() && 0 <= j < image[i].len() ==> 0 <= #[trigger] image[i][j] <= 1,
        ensures
            res.len() == image.len(),
            forall |i: int| 0 <= i < res.len() ==> #[trigger] res[i].len() == image.len(),
            forall |i: int, j: int| 0 <= i < image.len() && 0 <= j < image.len() ==>
                #[trigger] res[i][j] == 1 - image[i][image.len() - 1 - j],
    {
        let n = image.len();
        let mut result: Vec<Vec<i32>> = Vec::new();

        let mut i: usize = 0;
        while i < n
            invariant
                n == image.len(),
                1 <= n <= 20,
                i <= n,
                result.len() == i,
                forall |r: int| 0 <= r < n ==> #[trigger] image[r].len() == n,
                forall |r: int, c: int| 0 <= r < n && 0 <= c < n ==> 0 <= #[trigger] image[r][c] <= 1,
                forall |r: int| 0 <= r < i ==> #[trigger] result[r].len() == n,
                forall |r: int, c: int| 0 <= r < i && 0 <= c < n ==>
                    #[trigger] result[r][c] == 1 - image[r][n - 1 - c],
            decreases n - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    n == image.len(),
                    i < n,
                    j <= n,
                    row.len() == j,
                    forall |r: int| 0 <= r < n ==> #[trigger] image[r].len() == n,
                    forall |r: int, c: int| 0 <= r < n && 0 <= c < n ==> 0 <= #[trigger] image[r][c] <= 1,
                    forall |c: int| 0 <= c < j ==> #[trigger] row[c] == 1 - image[i as int][n as int - 1 - c],
                decreases n - j,
            {
                proof {
                    assert(image[i as int].len() == n);
                    assert(n - 1 - j < n);
                    assert(n - 1 - j < image[i as int].len());
                }
                row.push(1 - image[i][n - 1 - j]);
                j += 1;
            }

            result.push(row);
            i += 1;
        }

        result
    }
}

}
