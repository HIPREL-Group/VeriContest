use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min2(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn max2(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    
    pub open spec fn shelf_total_width(books: Seq<Vec<i32>>, start: int, end: int) -> int
        decreases end - start,
    {
        if start >= end { 0 }
        else { books[start][0] as int + Self::shelf_total_width(books, start + 1, end) }
    }

    
    pub open spec fn shelf_max_height(books: Seq<Vec<i32>>, start: int, end: int) -> int
        decreases end - start,
    {
        if start >= end { 0 }
        else { Self::max2(books[start][1] as int, Self::shelf_max_height(books, start + 1, end)) }
    }

    
    
    pub open spec fn is_valid_arrangement(books: Seq<Vec<i32>>, n: int, cuts: Seq<int>, shelf_width: int) -> bool {
        cuts.len() >= 1
        && cuts[0] == 0
        && cuts[cuts.len() - 1] == n
        && (forall |k: int| 0 <= k < cuts.len() - 1 ==>
            (#[trigger] cuts[k]) < cuts[k + 1]
            && Self::shelf_total_width(books, cuts[k], cuts[k + 1]) <= shelf_width)
    }

    
    pub open spec fn arrangement_height(books: Seq<Vec<i32>>, cuts: Seq<int>) -> int
        decreases cuts.len(),
    {
        if cuts.len() <= 1 { 0 }
        else {
            let k = (cuts.len() - 1) as int;
            Self::arrangement_height(books, cuts.take(k)) + Self::shelf_max_height(books, cuts[k - 1], cuts[k])
        }
    }

    pub open spec fn min_height_dp(books: Seq<Vec<i32>>, sw: int, i: int) -> int
        decreases i + 1, 0int,
    {
        if i <= 0 {
            0
        } else {
            Self::best_shelf(books, sw, i, i - 1, 0, 0)
        }
    }

    pub open spec fn best_shelf(books: Seq<Vec<i32>>, sw: int, i: int, j: int, width: int, height: int) -> int
        recommends
            0 <= j < i <= books.len(),
        decreases j + 1, 1int,
    {
        let new_width = width + books[j][0] as int;
        let new_height = Self::max2(height, books[j][1] as int);
        if new_width > sw {
            1_000_001
        } else {
            let candidate = Self::min_height_dp(books, sw, j) + new_height;
            if j <= 0 {
                candidate
            } else {
                Self::min2(candidate, Self::best_shelf(books, sw, i, j - 1, new_width, new_height))
            }
        }
    }

    proof fn min2_assoc(a: int, b: int, c: int)
        ensures
            Self::min2(a, Self::min2(b, c)) == Self::min2(Self::min2(a, b), c),
    {
    }

    proof fn dp_bounds(books: Seq<Vec<i32>>, sw: int, k: int)
        requires
            0 <= k <= books.len(),
            1 <= sw <= 1000,
            forall |i: int| 0 <= i < books.len() ==> (#[trigger] books[i]).len() == 2,
            forall |i: int| 0 <= i < books.len() ==> 1 <= (#[trigger] books[i][0]) as int <= sw,
            forall |i: int| 0 <= i < books.len() ==> 1 <= (#[trigger] books[i][1]) as int <= 1000,
        ensures
            0 <= Self::min_height_dp(books, sw, k) <= k * 1000,
        decreases k + 1, 0int,
    {
        if k > 0 {
            Self::shelf_bounds(books, sw, k, k - 1, 0, 0);
        }
    }

    proof fn shelf_bounds(books: Seq<Vec<i32>>, sw: int, n: int, j: int, width: int, height: int)
        requires
            0 <= j < n <= books.len(),
            1 <= sw <= 1000,
            0 <= width,
            0 <= height <= 1000,
            forall |i: int| 0 <= i < books.len() ==> (#[trigger] books[i]).len() == 2,
            forall |i: int| 0 <= i < books.len() ==> 1 <= (#[trigger] books[i][0]) as int <= sw,
            forall |i: int| 0 <= i < books.len() ==> 1 <= (#[trigger] books[i][1]) as int <= 1000,
        ensures
            Self::best_shelf(books, sw, n, j, width, height) >= 0,
            width + books[j][0] as int <= sw ==>
                Self::best_shelf(books, sw, n, j, width, height) <= n * 1000,
        decreases j + 1, 1int,
    {
        let new_width = width + books[j][0] as int;
        let new_height = Self::max2(height, books[j][1] as int);
        if new_width <= sw {
            Self::dp_bounds(books, sw, j);
            assert(1 <= new_height <= 1000);
            assert(Self::min_height_dp(books, sw, j) + new_height <= j * 1000 + 1000);
            assert(j * 1000 + 1000 <= n * 1000) by (nonlinear_arith)
                requires j < n;
            if j > 0 {
                Self::shelf_bounds(books, sw, n, j - 1, new_width, new_height);
            }
        }
    }

    

    proof fn shelf_max_height_bound(books: Seq<Vec<i32>>, start: int, end: int)
        requires
            0 <= start <= end <= books.len(),
            forall |i: int| 0 <= i < books.len() ==> (#[trigger] books[i]).len() == 2,
            forall |i: int| 0 <= i < books.len() ==> 1 <= (#[trigger] books[i][1]) as int <= 1000,
        ensures
            0 <= Self::shelf_max_height(books, start, end) <= 1000,
        decreases end - start,
    {
        if start < end {
            Self::shelf_max_height_bound(books, start + 1, end);
        }
    }

    proof fn cuts_nonneg(cuts: Seq<int>, k: int)
        requires
            cuts.len() >= 1,
            cuts[0] == 0,
            forall |i: int| 0 <= i < cuts.len() - 1 ==> (#[trigger] cuts[i]) < cuts[i + 1],
            0 <= k < cuts.len(),
        ensures
            cuts[k] >= 0,
        decreases k,
    {
        if k > 0 {
            Self::cuts_nonneg(cuts, k - 1);
        }
    }

    proof fn total_width_mono(books: Seq<Vec<i32>>, start1: int, start2: int, end: int)
        requires
            0 <= start1 <= start2 <= end <= books.len(),
            forall |i: int| 0 <= i < books.len() ==> (#[trigger] books[i]).len() == 2,
            forall |i: int| 0 <= i < books.len() ==> (#[trigger] books[i][0]) as int >= 1,
        ensures
            Self::shelf_total_width(books, start2, end) <= Self::shelf_total_width(books, start1, end),
        decreases end - start1,
    {
        if start1 < start2 {
            Self::total_width_mono(books, start1 + 1, start2, end);
        }
    }

    proof fn best_shelf_le_candidate(
        books: Seq<Vec<i32>>, sw: int, n: int,
        j_cur: int, j_target: int,
        w: int, h: int,
    )
        requires
            0 <= j_target <= j_cur < n <= books.len(),
            1 <= sw <= 1000,
            w == Self::shelf_total_width(books, j_cur + 1, n),
            h == Self::shelf_max_height(books, j_cur + 1, n),
            Self::shelf_total_width(books, j_target, n) <= sw,
            forall |i: int| 0 <= i < books.len() ==> (#[trigger] books[i]).len() == 2,
            forall |i: int| 0 <= i < books.len() ==> 1 <= (#[trigger] books[i][0]) as int <= sw,
            forall |i: int| 0 <= i < books.len() ==> 1 <= (#[trigger] books[i][1]) as int <= 1000,
        ensures
            Self::best_shelf(books, sw, n, j_cur, w, h) <=
                Self::min_height_dp(books, sw, j_target) + Self::shelf_max_height(books, j_target, n),
        decreases j_cur - j_target,
    {
        Self::total_width_mono(books, j_target, j_cur, n);
        if j_cur > j_target {
            let new_width = w + books[j_cur][0] as int;
            let new_height = Self::max2(h, books[j_cur][1] as int);
            Self::best_shelf_le_candidate(
                books, sw, n, j_cur - 1, j_target, new_width, new_height,
            );
        }
    }

    proof fn valid_arrangement_prefix(books: Seq<Vec<i32>>, n: int, cuts: Seq<int>, sw: int)
        requires
            Self::is_valid_arrangement(books, n, cuts, sw),
            cuts.len() >= 2,
        ensures
            Self::is_valid_arrangement(books, cuts[cuts.len() - 2], cuts.take((cuts.len() - 1) as int), sw),
    {
        let m = (cuts.len() - 1) as int;
        let sub = cuts.take(m);
        assert forall |k: int| 0 <= k < sub.len() - 1 implies
            (#[trigger] sub[k]) < sub[k + 1]
            && Self::shelf_total_width(books, sub[k], sub[k + 1]) <= sw
        by {
            assert(sub[k] == cuts[k]);
            assert(sub[k + 1] == cuts[k + 1]);
        }
    }

    proof fn valid_arrangement_extend(books: Seq<Vec<i32>>, j: int, n: int, sub_cuts: Seq<int>, sw: int)
        requires
            Self::is_valid_arrangement(books, j, sub_cuts, sw),
            0 <= j < n,
            Self::shelf_total_width(books, j, n) <= sw,
        ensures
            Self::is_valid_arrangement(books, n, sub_cuts.push(n), sw),
    {
        let ext = sub_cuts.push(n);
        assert forall |k: int| 0 <= k < ext.len() - 1 implies
            (#[trigger] ext[k]) < ext[k + 1]
            && Self::shelf_total_width(books, ext[k], ext[k + 1]) <= sw
        by {
            if k < sub_cuts.len() - 1 {
                assert(ext[k] == sub_cuts[k]);
                assert(ext[k + 1] == sub_cuts[k + 1]);
            } else {
                assert(ext[k] == sub_cuts[sub_cuts.len() - 1]);
                assert(ext[k + 1] == n);
            }
        }
    }

    proof fn arrangement_height_extend(books: Seq<Vec<i32>>, sub_cuts: Seq<int>, n: int)
        requires
            sub_cuts.len() >= 1,
        ensures
            Self::arrangement_height(books, sub_cuts.push(n)) ==
                Self::arrangement_height(books, sub_cuts)
                + Self::shelf_max_height(books, sub_cuts[sub_cuts.len() - 1], n),
    {
        let ext = sub_cuts.push(n);
        let k = (ext.len() - 1) as int;
        assert(ext.take(k) =~= sub_cuts);
    }

    proof fn best_shelf_has_witness(
        books: Seq<Vec<i32>>, sw: int, n: int,
        j: int, w: int, h: int,
    )
        requires
            0 <= j < n <= books.len(),
            n <= 1000,
            1 <= sw <= 1000,
            w == Self::shelf_total_width(books, j + 1, n),
            h == Self::shelf_max_height(books, j + 1, n),
            w + books[j][0] as int <= sw,
            forall |i: int| 0 <= i < books.len() ==> (#[trigger] books[i]).len() == 2,
            forall |i: int| 0 <= i < books.len() ==> 1 <= (#[trigger] books[i][0]) as int <= sw,
            forall |i: int| 0 <= i < books.len() ==> 1 <= (#[trigger] books[i][1]) as int <= 1000,
        ensures
            exists |j_star: int|
                0 <= j_star <= j
                && Self::shelf_total_width(books, j_star, n) <= sw
                && Self::best_shelf(books, sw, n, j, w, h) ==
                    Self::min_height_dp(books, sw, j_star) + Self::shelf_max_height(books, j_star, n),
        decreases j,
    {
        let new_width = w + books[j][0] as int;
        let new_height = Self::max2(h, books[j][1] as int);
        let candidate = Self::min_height_dp(books, sw, j) + new_height;

        
        assert(Self::shelf_total_width(books, j, n) == new_width);
        
        assert(Self::shelf_max_height(books, j, n) == new_height);

        if j <= 0 {
            assert(j == 0);
            
            assert(Self::best_shelf(books, sw, n, j, w, h) == candidate);
            
            assert(Self::min_height_dp(books, sw, 0) == 0int);
            assert(Self::best_shelf(books, sw, n, j, w, h) ==
                Self::min_height_dp(books, sw, 0) + Self::shelf_max_height(books, 0, n));
        } else {
            let sub_new_width = new_width + books[j - 1][0] as int;
            if sub_new_width > sw {
                
                Self::dp_bounds(books, sw, j);
                Self::shelf_max_height_bound(books, j + 1, n);
                assert(h <= 1000);
                assert(new_height <= 1000);
                assert(candidate <= j * 1000 + 1000);
                assert(j * 1000 + 1000 <= 1_000_000) by (nonlinear_arith)
                    requires 0 <= j, j <= 999;
                assert(candidate < 1_000_001int);
                
                
                assert(Self::best_shelf(books, sw, n, j - 1, new_width, new_height) == 1_000_001int);
                
                assert(Self::best_shelf(books, sw, n, j, w, h) ==
                    Self::min2(candidate, Self::best_shelf(books, sw, n, j - 1, new_width, new_height)));
                assert(Self::best_shelf(books, sw, n, j, w, h) == candidate);
                
                assert(Self::best_shelf(books, sw, n, j, w, h) ==
                    Self::min_height_dp(books, sw, j) + Self::shelf_max_height(books, j, n));
            } else {
                Self::best_shelf_has_witness(books, sw, n, j - 1, new_width, new_height);
                let sub_val = Self::best_shelf(books, sw, n, j - 1, new_width, new_height);
                if candidate <= sub_val {
                    
                    assert(Self::best_shelf(books, sw, n, j, w, h) == candidate);
                    
                    assert(Self::best_shelf(books, sw, n, j, w, h) ==
                        Self::min_height_dp(books, sw, j) + Self::shelf_max_height(books, j, n));
                } else {
                    
                    assert(Self::best_shelf(books, sw, n, j, w, h) == sub_val);
                }
            }
        }
    }

    proof fn dp_optimal(books: Seq<Vec<i32>>, sw: int, n: int)
        requires
            0 <= n <= books.len(),
            n <= 1000,
            1 <= sw <= 1000,
            forall |i: int| 0 <= i < books.len() ==> (#[trigger] books[i]).len() == 2,
            forall |i: int| 0 <= i < books.len() ==> 1 <= (#[trigger] books[i][0]) as int <= sw,
            forall |i: int| 0 <= i < books.len() ==> 1 <= (#[trigger] books[i][1]) as int <= 1000,
        ensures
            forall |cuts: Seq<int>| Self::is_valid_arrangement(books, n, cuts, sw) ==>
                #[trigger] Self::arrangement_height(books, cuts) >= Self::min_height_dp(books, sw, n),
        decreases n,
    {
        assert forall |cuts: Seq<int>| Self::is_valid_arrangement(books, n, cuts, sw) implies
            #[trigger] Self::arrangement_height(books, cuts) >= Self::min_height_dp(books, sw, n)
        by {
            if n <= 0 {
                
                assert(Self::min_height_dp(books, sw, n) == 0int);
                
                if cuts.len() >= 2 {
                    
                    assert(cuts[0] < cuts[1]);
                    
                    Self::cuts_nonneg(cuts, (cuts.len() - 2) as int);
                    assert(cuts[(cuts.len() - 2) as int] >= 0);
                    assert(cuts[(cuts.len() - 2) as int] < cuts[(cuts.len() - 1) as int]);
                    assert(cuts[(cuts.len() - 1) as int] == n);
                    
                    assert(false);
                }
                assert(cuts.len() == 1);
                assert(Self::arrangement_height(books, cuts) == 0int);
            } else {
                assert(cuts.len() >= 2) by {
                    if cuts.len() < 2 {
                        assert(cuts[0] == 0);
                        assert(cuts[cuts.len() - 1] == n);
                    }
                }
                let m = (cuts.len() - 1) as int;
                let j = cuts[m - 1];
                let sub_cuts = cuts.take(m);

                assert(j < n) by { assert(cuts[m - 1] < cuts[m]); }
                Self::cuts_nonneg(cuts, m - 1);
                assert(j >= 0);
                assert(cuts[m] == n);
                assert(Self::shelf_total_width(books, j, n) <= sw);

                Self::valid_arrangement_prefix(books, n, cuts, sw);
                assert(cuts.take(m) =~= sub_cuts);

                Self::dp_optimal(books, sw, j);
                assert(Self::arrangement_height(books, sub_cuts) >= Self::min_height_dp(books, sw, j));

                
                assert(Self::shelf_total_width(books, n, n) == 0int);
                assert(Self::shelf_max_height(books, n, n) == 0int);

                Self::best_shelf_le_candidate(books, sw, n, n - 1, j,
                    Self::shelf_total_width(books, n as int, n),
                    Self::shelf_max_height(books, n as int, n));

                
                assert(n > 0int);
                assert(Self::min_height_dp(books, sw, n) == Self::best_shelf(books, sw, n, n - 1, 0, 0));
                assert(Self::min_height_dp(books, sw, n) <=
                    Self::min_height_dp(books, sw, j) + Self::shelf_max_height(books, j, n));

                assert(Self::arrangement_height(books, cuts) ==
                    Self::arrangement_height(books, sub_cuts) + Self::shelf_max_height(books, j, n));
                assert(Self::arrangement_height(books, cuts) >=
                    Self::min_height_dp(books, sw, j) + Self::shelf_max_height(books, j, n));
                
                assert(Self::arrangement_height(books, cuts) >= Self::min_height_dp(books, sw, n));
            }
        }
    }

    proof fn dp_achievable(books: Seq<Vec<i32>>, sw: int, n: int)
        requires
            0 <= n <= books.len(),
            n <= 1000,
            1 <= sw <= 1000,
            forall |i: int| 0 <= i < books.len() ==> (#[trigger] books[i]).len() == 2,
            forall |i: int| 0 <= i < books.len() ==> 1 <= (#[trigger] books[i][0]) as int <= sw,
            forall |i: int| 0 <= i < books.len() ==> 1 <= (#[trigger] books[i][1]) as int <= 1000,
        ensures
            exists |cuts: Seq<int>| #[trigger] Self::is_valid_arrangement(books, n, cuts, sw)
                && Self::arrangement_height(books, cuts) == Self::min_height_dp(books, sw, n),
        decreases n,
    {
        if n <= 0 {
            let cuts = seq![0int];
            assert(Self::is_valid_arrangement(books, 0, cuts, sw));
            assert(Self::arrangement_height(books, cuts) == 0);
        } else {
            assert(0 + books[n - 1][0] as int <= sw);

            Self::best_shelf_has_witness(books, sw, n, n - 1,
                Self::shelf_total_width(books, n as int, n),
                Self::shelf_max_height(books, n as int, n));

            let j_star = choose |j_star: int|
                0 <= j_star <= n - 1
                && Self::shelf_total_width(books, j_star, n) <= sw
                && Self::best_shelf(books, sw, n, n - 1, 0, 0) ==
                    Self::min_height_dp(books, sw, j_star) + Self::shelf_max_height(books, j_star, n);

            assert(0 <= j_star && j_star < n);

            Self::dp_achievable(books, sw, j_star);
            let sub_cuts = choose |cuts: Seq<int>|
                #[trigger] Self::is_valid_arrangement(books, j_star, cuts, sw)
                && Self::arrangement_height(books, cuts) == Self::min_height_dp(books, sw, j_star);

            let cuts = sub_cuts.push(n);
            Self::valid_arrangement_extend(books, j_star, n, sub_cuts, sw);
            Self::arrangement_height_extend(books, sub_cuts, n);
        }
    }

    pub fn min_height_shelves(books: Vec<Vec<i32>>, shelf_width: i32) -> (res: i32)
        requires
            1 <= books.len() <= 1000,
            1 <= shelf_width <= 1000,
            forall |i: int| 0 <= i < books.len() ==> #[trigger] books[i].len() == 2,
            forall |i: int| 0 <= i < books.len() ==> 1 <= #[trigger] books[i][0] <= shelf_width,
            forall |i: int| 0 <= i < books.len() ==> 1 <= #[trigger] books[i][1] <= 1000,
        ensures
            exists |cuts: Seq<int>| #[trigger] Self::is_valid_arrangement(books@, books.len() as int, cuts, shelf_width as int)
                && Self::arrangement_height(books@, cuts) == res as int,
            forall |cuts: Seq<int>| Self::is_valid_arrangement(books@, books.len() as int, cuts, shelf_width as int)
                ==> res as int <= #[trigger] Self::arrangement_height(books@, cuts),
    {
        let n = books.len();
        let sw = shelf_width;
        let mut dp: Vec<i32> = Vec::new();
        dp.push(0);
        let mut i: usize = 1;

        while i <= n
            invariant
                dp@.len() == i as int,
                1 <= i <= n + 1,
                n == books.len(),
                1 <= n <= 1000,
                sw == shelf_width,
                1 <= sw <= 1000,
                forall |k: int| 0 <= k < books.len() ==> (#[trigger] books[k]).len() == 2,
                forall |k: int| 0 <= k < books.len() ==> 1 <= (#[trigger] books[k][0]) as int <= sw as int,
                forall |k: int| 0 <= k < books.len() ==> 1 <= (#[trigger] books[k][1]) as int <= 1000,
                forall |k: int| 0 <= k < i as int ==> (#[trigger] dp@[k]) as int == Self::min_height_dp(books@, sw as int, k),
                forall |k: int| 0 <= k < i as int ==> 0 <= (#[trigger] dp@[k]) as int <= k * 1000,
            decreases n + 1 - i,
        {
            let ghost sw_int = sw as int;
            let ghost i_int = i as int;

            proof {
                Self::dp_bounds(books@, sw_int, i_int);
            }

            let mut width: i32 = 0;
            let mut height: i32 = 0;
            let mut best: i32 = 1_000_001;
            let mut j: usize = i;
            let mut stopped: bool = false;
            let ghost mut remaining: int = Self::best_shelf(books@, sw_int, i_int, i_int - 1, 0, 0);

            while j > 0 && !stopped
                invariant
                    0 <= j <= i,
                    1 <= i <= n,
                    1 <= n <= 1000,
                    n == books.len(),
                    sw == shelf_width,
                    1 <= sw <= 1000,
                    dp@.len() == i as int,
                    forall |k: int| 0 <= k < books.len() ==> (#[trigger] books[k]).len() == 2,
                    forall |k: int| 0 <= k < books.len() ==> 1 <= (#[trigger] books[k][0]) as int <= sw as int,
                    forall |k: int| 0 <= k < books.len() ==> 1 <= (#[trigger] books[k][1]) as int <= 1000,
                    forall |k: int| 0 <= k < i as int ==> (#[trigger] dp@[k]) as int == Self::min_height_dp(books@, sw as int, k),
                    forall |k: int| 0 <= k < i as int ==> 0 <= (#[trigger] dp@[k]) as int <= k * 1000,
                    !stopped ==> 0 <= width <= sw,
                    0 <= height <= 1000,
                    sw_int == sw as int,
                    i_int == i as int,
                    j as int == i_int ==> (width == 0i32 && height == 0i32 && !stopped),
                    j < i ==> 1 <= best as int <= i_int * 1000,
                    j as int == i_int ==> best == 1_000_001i32,
                    stopped ==> j < i,
                    remaining == (
                        if j as int == i_int {
                            Self::best_shelf(books@, sw_int, i_int, i_int - 1, 0, 0)
                        } else if j > 0 && !stopped {
                            Self::best_shelf(books@, sw_int, i_int, (j - 1) as int, width as int, height as int)
                        } else {
                            1_000_001int
                        }
                    ),
                    Self::min_height_dp(books@, sw_int, i_int) == Self::min2(best as int, remaining),
                decreases (if stopped { 0int } else { 1int }), j,
            {
                let book_thickness = books[j - 1][0];
                let book_height = books[j - 1][1];

                proof {
                    assert(1 <= book_thickness as int <= sw as int);
                    assert(1 <= book_height as int <= 1000);
                }

                let next_width = width + book_thickness;

                if next_width > shelf_width {
                    proof {
                        assert(j < i);
                        remaining = 1_000_001int;
                    }
                    stopped = true;
                } else {
                    proof {
                        Self::dp_bounds(books@, sw_int, (j - 1) as int);
                    }

                    j = j - 1;
                    width = next_width;
                    let new_height = if book_height > height { book_height } else { height };

                    proof {
                        let j_int = j as int;
                        assert(dp@[j_int] as int == Self::min_height_dp(books@, sw_int, j_int));
                        assert(0 <= dp@[j_int] as int <= j_int * 1000);
                        assert(j_int * 1000 <= 999_000int) by (nonlinear_arith)
                            requires 0 <= j_int, j_int <= 999;
                    }

                    let candidate = dp[j] + new_height;
                    let old_best = best;
                    if candidate < best {
                        best = candidate;
                    }
                    height = new_height;

                    proof {
                        let j_int = j as int;

                        if j > 0 {
                            remaining = Self::best_shelf(books@, sw_int, i_int, j_int - 1, width as int, height as int);
                            Self::min2_assoc(old_best as int, candidate as int, remaining);
                        } else {
                            remaining = 1_000_001int;
                        }

                        Self::shelf_bounds(books@, sw_int, i_int, j_int,
                            (width - book_thickness) as int,
                            (if book_height as int >= height as int { 0int } else { height as int }));
                    }
                }
            }

            proof {
                assert(j < i);
                assert(remaining == 1_000_001int);
                assert(Self::min_height_dp(books@, sw_int, i_int) == Self::min2(best as int, 1_000_001int));
                assert(best as int <= 1_000_000int);
                assert(best as int == Self::min_height_dp(books@, sw_int, i_int));
            }

            dp.push(best);

            proof {
                assert forall |k: int| 0 <= k < i_int + 1 implies (#[trigger] dp@[k]) as int == Self::min_height_dp(books@, sw as int, k) by {
                    if k < i_int {} else {}
                };
                assert forall |k: int| 0 <= k < i_int + 1 implies 0 <= (#[trigger] dp@[k]) as int <= k * 1000 by {
                    if k < i_int {} else {
                        Self::dp_bounds(books@, sw_int, i_int);
                    }
                };
            }

            i = i + 1;
        }

        proof {
            let n_int = n as int;
            let sw_int = sw as int;
            assert(dp@[n_int] as int == Self::min_height_dp(books@, sw_int, n_int));

            Self::dp_achievable(books@, sw_int, n_int);
            Self::dp_optimal(books@, sw_int, n_int);
        }

        dp[n]
    }
}

}
