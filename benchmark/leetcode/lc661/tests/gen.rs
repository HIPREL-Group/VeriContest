use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    rows: usize,
    cols: usize,
    val: i32,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= rows <= 200,
        1 <= cols <= 200,
        0 <= val <= 255,
    ensures
        1 <= result.len() <= 200,
        1 <= result[0].len() <= 200,
        forall |i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == result[0].len(),
        forall |i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 0 <= #[trigger] result[i][j] <= 255,
{
    // Determine pixel value based on mutation
    let pixel: i32 = if mutation_kind == 0 {
        val                                           // identity
    } else if mutation_kind == 1 && val < 255 {
        (val + 1) as i32                              // nudge up
    } else if mutation_kind == 2 && val > 0 {
        (val - 1) as i32                              // nudge down
    } else if mutation_kind == 3 {
        0                                             // zero
    } else if mutation_kind == 4 {
        255                                           // max boundary
    } else if mutation_kind == 5 {
        val / 2                                       // halve
    } else if mutation_kind == 6 {
        if val <= 127 { (val * 2) as i32 } else { val } // double
    } else if mutation_kind == 7 {
        (255 - val) as i32                            // complement
    } else if mutation_kind == 8 {
        1                                             // small nonzero
    } else if mutation_kind == 9 {
        128                                           // midpoint
    } else {
        val                                           // fallback
    };

    // Build the 2D image: rows x cols filled with pixel
    let mut img: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < rows
        invariant
            0 <= r <= rows,
            img.len() == r,
            1 <= rows <= 200,
            1 <= cols <= 200,
            0 <= pixel <= 255,
            forall |i: int| 0 <= i < r as int ==> #[trigger] img[i].len() == cols,
            forall |i: int, j: int| 0 <= i < r as int && 0 <= j < img[i].len() as int
                ==> 0 <= #[trigger] img[i][j] <= 255,
        decreases rows - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < cols
            invariant
                0 <= c <= cols,
                row.len() == c,
                1 <= cols <= 200,
                0 <= pixel <= 255,
                forall |j: int| 0 <= j < c as int ==> row[j] == pixel,
                forall |j: int| 0 <= j < c as int ==> 0 <= #[trigger] row[j] <= 255,
            decreases cols - c,
        {
            row.push(pixel);
            c += 1;
        }
        img.push(row);
        r += 1;
    }
    img
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

fn random_image(rng: &mut Rng, rows: usize, cols: usize) -> Vec<Vec<i32>> {
    let mut img = Vec::with_capacity(rows);
    for _ in 0..rows {
        let mut row = Vec::with_capacity(cols);
        for _ in 0..cols {
            row.push(rng.gen_range_i64(0, 255) as i32);
        }
        img.push(row);
    }
    img
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |img: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", img);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::image_smoother(img.clone());
        writeln!(out, "{}", json!({"input": {"img": img}, "output": output})).unwrap();
        *count += 1;
    };

    // Example 1 from description.md
    emit(vec![vec![1,1,1], vec![1,0,1], vec![1,1,1]], &mut seen, &mut out, &mut count);
    // Example 2 from description.md
    emit(vec![vec![100,200,100], vec![200,50,200], vec![100,200,100]], &mut seen, &mut out, &mut count);

    // Verified generator: seed pools × mutation kinds
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let seed_vals: Vec<i32> = vec![0, 1, 127, 128, 255, 50, 200, 10, 254];

    // Small fixed-size images through the verified generator
    let size_pairs: Vec<(usize, usize)> = vec![
        (1, 1), (1, 2), (2, 1), (2, 2), (3, 3),
        (1, 200), (200, 1), (5, 5), (10, 10),
    ];
    for &(rows, cols) in &size_pairs {
        for &sv in &seed_vals {
            for &mk in &mutation_kinds {
                if count >= target { break; }
                let img = generate_test_case(rows, cols, sv, mk);
                emit(img, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random images with diverse sizes through verified generator
    for _ in 0..200 {
        if count >= target { break; }
        let rows = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 50),      // medium
            3 => rng.gen_range_usize(51, 150),     // large
            _ => rng.gen_range_usize(150, 200),    // max
        };
        let cols = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 150),
            _ => rng.gen_range_usize(150, 200),
        };
        let val = if rng.gen_range_usize(0, 4) == 0 {
            *[0i32, 1, 127, 128, 255].get(rng.gen_range_usize(0, 4)).unwrap()
        } else {
            rng.gen_range_i64(0, 255) as i32
        };
        let mk = rng.gen_range_usize(0, 9) as u8;
        let img = generate_test_case(rows, cols, val, mk);
        emit(img, &mut seen, &mut out, &mut count);
    }

    // Fully random per-pixel images for diversity (not through verified generator)
    while count < target {
        let rows = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 150),
            _ => rng.gen_range_usize(150, 200),
        };
        let cols = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 150),
            _ => rng.gen_range_usize(150, 200),
        };
        let img = random_image(&mut rng, rows, cols);
        emit(img, &mut seen, &mut out, &mut count);
    }
}
