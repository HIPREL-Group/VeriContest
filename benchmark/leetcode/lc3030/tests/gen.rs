use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    image: Vec<Vec<i32>>,
    threshold: i32,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        3 <= image.len() <= 500,
        forall|r: int| 0 <= r < image.len() ==> #[trigger] image[r].len() == image[0].len(),
        3 <= image[0].len() <= 500,
        forall|r: int, c: int| 0 <= r < image.len() && 0 <= c < image[r].len()
            ==> 0 <= #[trigger] image[r][c] <= 255,
        0 <= threshold <= 255,
    ensures
        3 <= result.0.len() <= 500,
        forall|r: int| 0 <= r < result.0.len() ==> #[trigger] result.0[r].len() == result.0[0].len(),
        3 <= result.0[0].len() <= 500,
        forall|r: int, c: int| 0 <= r < result.0.len() && 0 <= c < result.0[r].len()
            ==> 0 <= #[trigger] result.0[r][c] <= 255,
        0 <= result.1 <= 255,
{
    if mutation_kind == 0 {
        // identity
        (image, threshold)
    } else if mutation_kind == 1 {
        // strictest threshold
        (image, 0)
    } else if mutation_kind == 2 {
        // loosest threshold
        (image, 255)
    } else if mutation_kind == 3 && threshold < 255 {
        // nudge threshold up
        (image, threshold + 1)
    } else if mutation_kind == 4 && threshold > 0 {
        // nudge threshold down
        (image, threshold - 1)
    } else if mutation_kind == 5 {
        // halve threshold
        (image, threshold / 2)
    } else if mutation_kind == 6 {
        // build uniform all-zero image with same dimensions
        let num_rows = image.len();
        let num_cols = image[0].len();
        let mut img: Vec<Vec<i32>> = Vec::new();
        let mut r: usize = 0;
        while r < num_rows
            invariant
                0 <= r <= num_rows,
                img.len() == r as int,
                3 <= num_rows <= 500,
                3 <= num_cols <= 500,
                forall|i: int| 0 <= i < r as int
                    ==> (#[trigger] img[i]).len() == num_cols,
                forall|i: int, j: int| 0 <= i < r as int && 0 <= j < num_cols as int
                    ==> #[trigger] img[i][j] == 0i32,
            decreases num_rows - r,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut c: usize = 0;
            while c < num_cols
                invariant
                    0 <= c <= num_cols,
                    row.len() == c as int,
                    forall|j: int| 0 <= j < c as int ==> #[trigger] row[j] == 0i32,
                decreases num_cols - c,
            {
                row.push(0);
                c += 1;
            }
            img.push(row);
            r += 1;
        }
        (img, threshold)
    } else if mutation_kind == 7 {
        // build uniform all-255 image with same dimensions
        let num_rows = image.len();
        let num_cols = image[0].len();
        let mut img: Vec<Vec<i32>> = Vec::new();
        let mut r: usize = 0;
        while r < num_rows
            invariant
                0 <= r <= num_rows,
                img.len() == r as int,
                3 <= num_rows <= 500,
                3 <= num_cols <= 500,
                forall|i: int| 0 <= i < r as int
                    ==> (#[trigger] img[i]).len() == num_cols,
                forall|i: int, j: int| 0 <= i < r as int && 0 <= j < num_cols as int
                    ==> #[trigger] img[i][j] == 255i32,
            decreases num_rows - r,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut c: usize = 0;
            while c < num_cols
                invariant
                    0 <= c <= num_cols,
                    row.len() == c as int,
                    forall|j: int| 0 <= j < c as int ==> #[trigger] row[j] == 255i32,
                decreases num_cols - c,
            {
                row.push(255);
                c += 1;
            }
            img.push(row);
            r += 1;
        }
        (img, threshold)
    } else {
        // fallback: identity
        (image, threshold)
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

struct Solution;
include!("../code.rs");

fn mutate(image: Vec<Vec<i32>>, threshold: i32, mutation_kind: u8) -> (Vec<Vec<i32>>, i32) {
    generate_test_case(image, threshold, mutation_kind)
}

fn random_image(rng: &mut Rng, rows: usize, cols: usize) -> Vec<Vec<i32>> {
    let mut image = Vec::with_capacity(rows);
    for _ in 0..rows {
        let mut row = Vec::with_capacity(cols);
        for _ in 0..cols {
            row.push(rng.gen_range_i64(0, 255) as i32);
        }
        image.push(row);
    }
    image
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3030);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut total = 0usize;

    let mut emit = |image: Vec<Vec<i32>>, threshold: i32,
                    out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let result = Solution::result_grid(image.clone(), threshold);
        writeln!(out, "{}", json!({
            "input": {"image": image, "threshold": threshold},
            "output": result
        })).unwrap();
        *total += 1;
    };

    // Examples from description.md
    emit(
        vec![vec![5,6,7,10], vec![8,9,10,10], vec![11,12,13,10]],
        3, &mut out, &mut total,
    );
    emit(
        vec![vec![10,20,30], vec![15,25,35], vec![20,30,40], vec![25,35,45]],
        12, &mut out, &mut total,
    );
    emit(
        vec![vec![5,6,7], vec![8,9,10], vec![11,12,13]],
        1, &mut out, &mut total,
    );

    // Seed images × mutation kinds
    let seed_images: Vec<(Vec<Vec<i32>>, i32)> = vec![
        // 3×3 uniform
        (vec![vec![0,0,0], vec![0,0,0], vec![0,0,0]], 0),
        (vec![vec![255,255,255], vec![255,255,255], vec![255,255,255]], 255),
        (vec![vec![128,128,128], vec![128,128,128], vec![128,128,128]], 10),
        // 3×3 gradient
        (vec![vec![0,1,2], vec![3,4,5], vec![6,7,8]], 1),
        (vec![vec![0,1,2], vec![3,4,5], vec![6,7,8]], 5),
        // 3×4 varying
        (vec![vec![10,20,30,40], vec![50,60,70,80], vec![90,100,110,120]], 15),
        // 4×3 with high contrast
        (vec![vec![0,255,0], vec![255,0,255], vec![0,255,0], vec![255,0,255]], 100),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    for (img, thr) in &seed_images {
        for &mk in &mutation_kinds {
            let (m_img, m_thr) = mutate(img.clone(), *thr, mk);
            emit(m_img, m_thr, &mut out, &mut total);
        }
    }

    // Random images with size classes and diverse thresholds
    while total < count {
        let (rows, cols) = match total % 5 {
            0 => (3usize, 3usize),
            1 => (rng.gen_range_usize(3, 10), rng.gen_range_usize(3, 10)),
            2 => (rng.gen_range_usize(10, 50), rng.gen_range_usize(10, 50)),
            3 => (rng.gen_range_usize(50, 100), rng.gen_range_usize(50, 100)),
            _ => (rng.gen_range_usize(100, 500), rng.gen_range_usize(100, 500)),
        };
        let threshold = match total % 7 {
            0 => 0i32,
            1 => 255,
            2 => 1,
            3 => 128,
            _ => rng.gen_range_i64(0, 255) as i32,
        };
        let image = random_image(&mut rng, rows, cols);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let (m_img, m_thr) = mutate(image, threshold, mk);
        emit(m_img, m_thr, &mut out, &mut total);
    }
}
