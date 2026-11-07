use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    thicknesses: &Vec<i32>,
    heights: &Vec<i32>,
    shelf_width: i32,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        1 <= thicknesses.len() <= 1000,
        thicknesses.len() == heights.len(),
        1 <= shelf_width <= 1000,
        forall|i: int| 0 <= i < thicknesses.len() ==> 1 <= #[trigger] thicknesses[i] <= 1000,
        forall|i: int| 0 <= i < heights.len() ==> 1 <= #[trigger] heights[i] <= 1000,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1 <= 1000,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == 2,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i][0] <= result.1,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i][1] <= 1000,
{
    // Determine effective shelf width based on mutation
    let sw: i32 = if mutation_kind == 1 {
        1000i32       // wide shelf
    } else if mutation_kind == 2 {
        1i32          // narrow shelf
    } else {
        shelf_width
    };

    let n = thicknesses.len();
    let mut books: Vec<Vec<i32>> = Vec::new();
    let mut idx: usize = 0;

    while idx < n
        invariant
            0 <= idx <= n,
            n == thicknesses.len(),
            n == heights.len(),
            1 <= n <= 1000,
            1 <= sw <= 1000,
            books.len() == idx,
            forall|j: int| 0 <= j < idx as int ==> #[trigger] books[j].len() == 2,
            forall|j: int| 0 <= j < idx as int ==> 1 <= #[trigger] books[j][0] <= sw,
            forall|j: int| 0 <= j < idx as int ==> 1 <= #[trigger] books[j][1] <= 1000,
            forall|k: int| 0 <= k < thicknesses.len() ==> 1 <= #[trigger] thicknesses[k] <= 1000,
            forall|k: int| 0 <= k < heights.len() ==> 1 <= #[trigger] heights[k] <= 1000,
        decreases n - idx,
    {
        let t_raw = thicknesses[idx];
        let h_raw = heights[idx];

        // Apply thickness mutation
        let t: i32 = if mutation_kind == 5 {
            1i32           // all thin books
        } else if mutation_kind == 6 {
            sw             // all books fill shelf
        } else if t_raw <= sw {
            t_raw          // within range
        } else {
            sw             // clamp to shelf width
        };

        // Apply height mutation
        let h: i32 = if mutation_kind == 3 {
            1i32           // all min height
        } else if mutation_kind == 4 {
            1000i32        // all max height
        } else {
            h_raw
        };

        let mut book: Vec<i32> = Vec::new();
        book.push(t);
        book.push(h);

        assert(book.len() == 2);
        assert(book[0] == t);
        assert(book[1] == h);

        books.push(book);
        idx += 1;
    }

    (books, sw)
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

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut emitted = 0usize;

    let mut emit = |books: Vec<Vec<i32>>, shelf_width: i32,
                    out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let result = Solution::min_height_shelves(books.clone(), shelf_width);
        writeln!(out, "{}", json!({
            "input": {"books": books, "shelf_width": shelf_width},
            "output": result
        })).unwrap();
        *emitted += 1;
    };

    // Example 1
    emit(
        vec![vec![1,1],vec![2,3],vec![2,3],vec![1,1],vec![1,1],vec![1,1],vec![1,2]],
        4, &mut out, &mut emitted,
    );
    // Example 2
    emit(
        vec![vec![1,3],vec![2,4],vec![3,2]],
        6, &mut out, &mut emitted,
    );

    // Generate diverse test cases
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6];

    while emitted < count {
        // Choose n based on size class
        let n = match emitted % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 50),     // medium
            3 => rng.gen_range_usize(51, 200),    // large
            _ => rng.gen_range_usize(201, 1000),  // max
        };

        // Choose shelf_width with boundary values ~20% of the time
        let shelf_width: i32 = if emitted % 10 == 0 {
            1
        } else if emitted % 10 == 1 {
            1000
        } else {
            rng.gen_range_i64(1, 1000) as i32
        };

        let mut thicknesses: Vec<i32> = Vec::new();
        let mut heights: Vec<i32> = Vec::new();
        for _ in 0..n {
            thicknesses.push(rng.gen_range_i64(1, 1000) as i32);
            heights.push(rng.gen_range_i64(1, 1000) as i32);
        }

        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let (books, sw) = generate_test_case(&thicknesses, &heights, shelf_width, mk);
        emit(books, sw, &mut out, &mut emitted);
    }
}
