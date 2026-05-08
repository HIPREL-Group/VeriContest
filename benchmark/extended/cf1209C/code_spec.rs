use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn spec_c1_values(d: Seq<i32>, c: Seq<i32>, n: int) -> Seq<i32>
    decreases n,
{
    if n <= 0 {
        seq![]
    } else {
        let rest = spec_c1_values(d, c, n - 1);
        if c[n - 1] == 1 {
            rest + seq![d[n - 1]]
        } else {
            rest
        }
    }
}

pub open spec fn spec_c2_values(d: Seq<i32>, c: Seq<i32>, n: int) -> Seq<i32>
    decreases n,
{
    if n <= 0 {
        seq![]
    } else {
        let rest = spec_c2_values(d, c, n - 1);
        if c[n - 1] == 2 {
            rest + seq![d[n - 1]]
        } else {
            rest
        }
    }
}

pub open spec fn spec_merged_digits(d: Seq<i32>, c: Seq<i32>, n: int) -> Seq<i32> {
    spec_c1_values(d, c, n) + spec_c2_values(d, c, n)
}

pub open spec fn spec_adjacent_nondecreasing(s: Seq<i32>) -> bool {
    forall|i: int| #![trigger s[i]] 0 <= i < s.len() - 1 ==> s[i] <= s[i + 1]
}

pub open spec fn spec_valid_coloring(d: Seq<i32>, c: Seq<i32>) -> bool {
    d.len() == c.len()
        && (forall|i: int| 0 <= i < d.len() ==> #[trigger] c[i] == 1 || c[i] == 2)
        && spec_adjacent_nondecreasing(spec_merged_digits(d, c, d.len() as int))
}

pub struct Solution;

impl Solution {
    fn merge_valid(digits: &Vec<i32>, colors: &Vec<i32>, n: usize) -> (b: bool) {
        let mut merged: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            if colors[i] == 1 {
                merged.push(digits[i]);
            }
            i = i + 1;
        }
        i = 0;
        while i < n {
            if colors[i] == 2 {
                merged.push(digits[i]);
            }
            i = i + 1;
        }
        i = 0;
        while i + 1 < merged.len() {
            if merged[i] > merged[i + 1] {
                return false;
            }
            i = i + 1;
        }
        true
    }

    fn try_pivot(digits: &Vec<i32>, n: usize, x: i32) -> (r: Vec<i32>) {
        let mut last_lt: usize = n;
        let mut i: usize = 0;
        while i < n {
            if digits[i] < x {
                last_lt = i;
            }
            i = i + 1;
        }
        let mut colors: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            colors.push(0);
            j = j + 1;
        }
        i = 0;
        while i < n {
            let d = digits[i];
            let c = if d < x {
                1
            } else if d > x {
                2
            } else {
                if last_lt != n && i <= last_lt {
                    2
                } else {
                    1
                }
            };
            colors.set(i, c);
            i = i + 1;
        }
        if Solution::merge_valid(digits, &colors, n) {
            colors
        } else {
            vec![]
        }
    }

    pub fn paint_digits(digits: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= digits.len() <= 200_000,
            forall|i: int|
                #![trigger digits[i]]
                0 <= i < digits.len() as int ==> 0 <= #[trigger] digits[i] <= 9,
        ensures
            res.len() == 0 || res.len() == digits.len(),
            res.len() == digits.len() ==> spec_valid_coloring(digits@, res@),
    {
        let n = digits.len();
        let mut x: i32 = 0;
        while x <= 9 {
            let cand = Solution::try_pivot(&digits, n, x);
            if cand.len() == n {
                return cand;
            }
            x = x + 1;
        }
        vec![]
    }
}

}
