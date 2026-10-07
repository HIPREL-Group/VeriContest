use vstd::prelude::*;

verus! {

pub open spec fn interval_rows(list: Seq<Vec<i32>>) -> bool {
    forall |i: int| 0 <= i < list.len() ==> #[trigger] list[i].len() == 2
}

pub open spec fn valid_interval(list: Seq<Vec<i32>>, i: int) -> bool {
    0 <= list[i][0] < list[i][1] <= 1_000_000_000
}

pub open spec fn disjoint_at(list: Seq<Vec<i32>>, i: int) -> bool {
    list[i][1] < list[i + 1][0]
}

pub open spec fn sorted_disjoint(list: Seq<Vec<i32>>) -> bool {
    (forall |i: int| 0 <= i < list.len() ==> valid_interval(list, i))
    && (forall |i: int| 0 <= i < list.len() as int - 1 ==>
        #[trigger] disjoint_at(list, i))
}

/// Build a sorted-disjoint interval list from starts and gaps.
/// Each interval is [start_k, start_k + width_k) where
///   start_0 = base,
///   start_{k+1} = start_k + width_k + gap_k
/// widths[k] >= 1 ensures start < end for each interval.
/// gaps[k] >= 1 ensures end_k < start_{k+1} (disjointness).
pub fn generate_one_list(
    n: usize,
    base: i32,
    widths: &Vec<i32>,
    gaps: &Vec<i32>,
) -> (result: Vec<Vec<i32>>)
    requires
        n <= 1000,
        0 <= base,
        widths.len() == n,
        gaps.len() == n,
        forall|i: int| 0 <= i < n ==> 1 <= #[trigger] widths[i] <= 1000,
        forall|i: int| 0 <= i < n ==> 1 <= #[trigger] gaps[i] <= 1000,
        // upper bound to stay within 1_000_000_000
        base as int + 2000 * n <= 1_000_000_000,
    ensures
        result.len() == n,
        interval_rows(result@),
        sorted_disjoint(result@),
{
    let mut list: Vec<Vec<i32>> = Vec::new();
    let mut cursor: i32 = base;
    let mut k: usize = 0;

    while k < n
        invariant
            0 <= k <= n,
            n <= 1000,
            list.len() == k,
            widths.len() == n,
            gaps.len() == n,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] widths[i] <= 1000,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] gaps[i] <= 1000,
            base as int + 2000 * n <= 1_000_000_000,
            0 <= cursor,
            cursor as int <= base as int + 2000 * k,
            interval_rows(list@),
            sorted_disjoint(list@),
            k > 0 ==> list@[k as int - 1].len() == 2,
            k > 0 ==> list@[k as int - 1][1] < cursor,
            k > 0 ==> list@[k as int - 1][1] <= 1_000_000_000,
        decreases n - k,
    {
        let start = cursor;
        let end = cursor + widths[k];

        assert(0 <= start);
        assert(start < end);
        assert(end as int <= base as int + 2000 * k + 1000);
        assert(end as int <= 1_000_000_000);

        let interval = vec![start, end];

        let ghost old_list = list@;
        let ghost old_len = list.len();

        list.push(interval);

        proof {
            // list@[k] is the new interval
            assert(list@[k as int]@ =~= interval@);
            assert(list@[k as int].len() == 2);
            assert(list@[k as int][0] == start);
            assert(list@[k as int][1] == end);

            // new interval is valid
            assert(0 <= start < end <= 1_000_000_000);
            assert(valid_interval(list@, k as int));

            // old elements unchanged
            assert forall|i: int| 0 <= i < old_len implies list@[i] =~= old_list[i] by {};

            // interval_rows still holds
            assert(interval_rows(list@));

            // valid_interval for all i < k+1
            assert forall|i: int| 0 <= i < k + 1 implies valid_interval(list@, i) by {
                if i < old_len as int {
                    // old element, unchanged
                    assert(list@[i] =~= old_list[i]);
                    assert(list@[i].len() == old_list[i].len());
                    assert(list@[i][0] == old_list[i][0]);
                    assert(list@[i][1] == old_list[i][1]);
                    assert(sorted_disjoint(old_list));
                    assert(valid_interval(old_list, i));
                }
            };

            // disjointness for consecutive pairs up to k
            assert forall|i: int| 0 <= i < k as int implies #[trigger] disjoint_at(list@, i) by {
                if i < old_len as int - 1 {
                    assert(list@[i] =~= old_list[i]);
                    assert(list@[i + 1] =~= old_list[i + 1]);
                    assert(sorted_disjoint(old_list));
                    assert(disjoint_at(old_list, i));
                } else if i == old_len as int - 1 && k > 0 {
                    // i == k-1, connecting old last to new element
                    assert(list@[i] =~= old_list[i]);
                    assert(list@[i].len() == 2);
                    assert(list@[i][1] == old_list[i][1]);
                    assert(old_list[i][1] < cursor);
                    assert(cursor == start);
                    assert(list@[i + 1][0] == start);
                    assert(list@[i][1] < list@[i + 1][0]);
                }
            };

            assert(sorted_disjoint(list@));
        }

        // advance cursor past the end of this interval plus a gap
        cursor = end + gaps[k];

        k = k + 1;
    }

    proof {
        assert(sorted_disjoint(list@));
    }

    list
}

pub fn generate_test_case(
    n1: usize,
    n2: usize,
    base1: i32,
    base2: i32,
    widths1: &Vec<i32>,
    gaps1: &Vec<i32>,
    widths2: &Vec<i32>,
    gaps2: &Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, Vec<Vec<i32>>))
    requires
        n1 <= 1000,
        n2 <= 1000,
        n1 + n2 >= 1,
        0 <= base1,
        0 <= base2,
        widths1.len() == n1,
        gaps1.len() == n1,
        widths2.len() == n2,
        gaps2.len() == n2,
        forall|i: int| 0 <= i < n1 ==> 1 <= #[trigger] widths1[i] <= 1000,
        forall|i: int| 0 <= i < n1 ==> 1 <= #[trigger] gaps1[i] <= 1000,
        forall|i: int| 0 <= i < n2 ==> 1 <= #[trigger] widths2[i] <= 1000,
        forall|i: int| 0 <= i < n2 ==> 1 <= #[trigger] gaps2[i] <= 1000,
        base1 as int + 2000 * n1 <= 1_000_000_000,
        base2 as int + 2000 * n2 <= 1_000_000_000,
    ensures
        0 <= result.0.len() <= 1000,
        0 <= result.1.len() <= 1000,
        result.0.len() + result.1.len() >= 1,
        interval_rows(result.0@),
        interval_rows(result.1@),
        sorted_disjoint(result.0@),
        sorted_disjoint(result.1@),
{
    let first = generate_one_list(n1, base1, widths1, gaps1);
    let second = generate_one_list(n2, base2, widths2, gaps2);

    if mutation_kind == 1 && n1 > 0 && n2 > 0 {
        // swap: return (second, first)
        (second, first)
    } else {
        (first, second)
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

fn random_widths_gaps(rng: &mut Rng, n: usize, max_val: i32) -> (Vec<i32>, Vec<i32>) {
    let mut widths = Vec::new();
    let mut gaps = Vec::new();
    for _ in 0..n {
        widths.push(rng.gen_range_i64(1, max_val as i64) as i32);
        gaps.push(rng.gen_range_i64(1, max_val as i64) as i32);
    }
    (widths, gaps)
}

fn make_uniform(n: usize, val: i32) -> Vec<i32> {
    vec![val; n]
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(986);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($n1:expr, $n2:expr, $b1:expr, $b2:expr,
         $w1:expr, $g1:expr, $w2:expr, $g2:expr, $mk:expr) => {
            if count < goal {
                let (first_list, second_list) = generate_test_case(
                    $n1, $n2, $b1, $b2, &$w1, &$g1, &$w2, &$g2, $mk,
                );
                let result = Solution::interval_intersection(
                    first_list.clone(), second_list.clone(),
                );
                let line = json!({
                    "input": {
                        "firstList": first_list,
                        "secondList": second_list
                    },
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- LeetCode examples ----
    // Example 1: firstList = [[0,2],[5,10],[13,23],[24,25]],
    //            secondList = [[1,5],[8,12],[15,24],[25,26]]
    // Construct from widths/gaps: interval [s, s+w], gap g
    // first: [0,2],[5,10],[13,23],[24,25] => widths=[2,5,10,1], gaps=[3,3,1,1]
    // second: [1,5],[8,12],[15,24],[25,26] => widths=[4,4,9,1], gaps=[3,3,1,1]
    emit!(4, 4, 0, 1,
         vec![2,5,10,1], vec![3,3,1,1],
         vec![4,4,9,1], vec![3,3,1,1], 0);

    // Example 2: firstList = [[1,3],[5,9]], secondList = []
    emit!(2, 0, 1, 0,
         vec![2,4], vec![2,1],
         Vec::<i32>::new(), Vec::<i32>::new(), 0);

    // ---- Edge cases ----

    // One list empty, other has one interval
    emit!(1, 0, 0, 0,
         vec![5], vec![1],
         Vec::<i32>::new(), Vec::<i32>::new(), 0);

    emit!(0, 1, 0, 0,
         Vec::<i32>::new(), Vec::<i32>::new(),
         vec![5], vec![1], 0);

    // Single interval each, overlapping
    emit!(1, 1, 0, 3,
         vec![10], vec![1],
         vec![10], vec![1], 0);

    // Single interval each, non-overlapping
    emit!(1, 1, 0, 100,
         vec![5], vec![1],
         vec![5], vec![1], 0);

    // Identical single intervals
    emit!(1, 1, 0, 0,
         vec![10], vec![1],
         vec![10], vec![1], 0);

    // Swap mutation on examples
    emit!(4, 4, 0, 1,
         vec![2,5,10,1], vec![3,3,1,1],
         vec![4,4,9,1], vec![3,3,1,1], 1);

    // ---- Tiny arrays with all mutations ----
    for mk in 0u8..=1 {
        emit!(2, 3, 0, 5,
             vec![3, 4], vec![2, 1],
             vec![2, 3, 5], vec![3, 2, 1],
             mk);
    }

    // ---- Small arrays, uniform widths/gaps ----
    for n in [1usize, 2, 3, 5, 10] {
        let w = make_uniform(n, 5);
        let g = make_uniform(n, 5);
        emit!(n, n, 0, 2, w.clone(), g.clone(), w.clone(), g.clone(), 0);
    }

    // ---- One list much larger than the other ----
    {
        let n1 = 100usize;
        let n2 = 1usize;
        let (w1, g1) = (make_uniform(n1, 3), make_uniform(n1, 3));
        let (w2, g2) = (make_uniform(n2, 500), make_uniform(n2, 1));
        emit!(n1, n2, 0, 0, w1, g1, w2, g2, 0);
    }
    {
        let n1 = 1usize;
        let n2 = 100usize;
        let (w1, g1) = (make_uniform(n1, 500), make_uniform(n1, 1));
        let (w2, g2) = (make_uniform(n2, 3), make_uniform(n2, 3));
        emit!(n1, n2, 0, 0, w1, g1, w2, g2, 0);
    }

    // ---- Medium random arrays ----
    for _ in 0..10 {
        let n1 = rng.gen_range_usize(5, 50);
        let n2 = rng.gen_range_usize(5, 50);
        let max_wg = std::cmp::min(1000, 1_000_000_000i64 / (2 * std::cmp::max(n1, n2) as i64)) as i32;
        let max_wg = std::cmp::max(1, std::cmp::min(max_wg, 1000));
        let (w1, g1) = random_widths_gaps(&mut rng, n1, max_wg);
        let (w2, g2) = random_widths_gaps(&mut rng, n2, max_wg);
        let b1 = rng.gen_range_i64(0, 1000) as i32;
        let b2 = rng.gen_range_i64(0, 1000) as i32;
        let mk = (rng.gen_range_usize(0, 1)) as u8;
        emit!(n1, n2, b1, b2, w1, g1, w2, g2, mk);
    }

    // ---- Large random arrays ----
    for _ in 0..5 {
        let n1 = rng.gen_range_usize(100, 500);
        let n2 = rng.gen_range_usize(100, 500);
        let max_wg = std::cmp::min(1000, 1_000_000_000i64 / (2 * std::cmp::max(n1, n2) as i64)) as i32;
        let max_wg = std::cmp::max(1, std::cmp::min(max_wg, 1000));
        let (w1, g1) = random_widths_gaps(&mut rng, n1, max_wg);
        let (w2, g2) = random_widths_gaps(&mut rng, n2, max_wg);
        let b1 = rng.gen_range_i64(0, 100) as i32;
        let b2 = rng.gen_range_i64(0, 100) as i32;
        let mk = (rng.gen_range_usize(0, 1)) as u8;
        emit!(n1, n2, b1, b2, w1, g1, w2, g2, mk);
    }

    // ---- Max size arrays (1000 each), small widths/gaps ----
    {
        let n = 500usize;
        let w = make_uniform(n, 1);
        let g = make_uniform(n, 1);
        emit!(n, n, 0, 0, w.clone(), g.clone(), w.clone(), g.clone(), 0);
        emit!(n, n, 0, 0, w.clone(), g.clone(), w.clone(), g.clone(), 1);
    }

    // ---- Near max boundary values ----
    {
        let n = 10usize;
        let w = make_uniform(n, 1000);
        let g = make_uniform(n, 1000);
        let base = 999_980_000i32;
        emit!(n, n, base, base, w.clone(), g.clone(), w.clone(), g.clone(), 0);
    }

    // ---- All-overlapping: same base, same widths/gaps ----
    for n in [1usize, 5, 20] {
        let w = make_uniform(n, 10);
        let g = make_uniform(n, 10);
        emit!(n, n, 0, 0, w.clone(), g.clone(), w.clone(), g.clone(), 0);
    }

    // ---- No overlap: second list starts after first ends ----
    {
        let n = 5usize;
        let w = make_uniform(n, 5);
        let g = make_uniform(n, 5);
        emit!(n, n, 0, 500_000_000, w.clone(), g.clone(), w.clone(), g.clone(), 0);
    }

    // ---- Fill remaining with random ----
    while count < goal {
        let n1 = rng.gen_range_usize(0, 100);
        let n2 = rng.gen_range_usize(0, 100);
        let (n1, n2) = if n1 + n2 == 0 { (1, 0) } else { (n1, n2) };
        let max_wg = if std::cmp::max(n1, n2) == 0 { 1000 } else {
            std::cmp::min(1000, std::cmp::max(1,
                (1_000_000_000i64 / (2 * std::cmp::max(n1, n2) as i64)) as i32
            ))
        };
        let (w1, g1) = random_widths_gaps(&mut rng, n1, max_wg);
        let (w2, g2) = random_widths_gaps(&mut rng, n2, max_wg);
        let b1 = rng.gen_range_i64(0, std::cmp::max(0, 1000)) as i32;
        let b2 = rng.gen_range_i64(0, std::cmp::max(0, 1000)) as i32;
        let mk = (rng.gen_range_usize(0, 1)) as u8;
        emit!(n1, n2, b1, b2, w1, g1, w2, g2, mk);
    }

    eprintln!("Generated {} test cases", count);
}
