use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw_bl: Vec<Vec<i32>>, raw_tr: Vec<Vec<i32>>) -> (result: (Vec<Vec<i32>>, Vec<Vec<i32>>))
    ensures
        2 <= result.0.len() <= 1000,
        result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == 2,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i].len() == 2,
        forall|i: int, j: int| #![trigger result.0[i][j]] #![trigger result.1[i][j]]
            0 <= i < result.0.len() && 0 <= j < 2 ==> 1 <= result.0[i][j] < result.1[i][j] <= 10000000,
{
    let n = if raw_bl.len() < 2 { 2usize } else if raw_bl.len() > 1000 { 1000usize } else { raw_bl.len() };
    let mut bl: Vec<Vec<i32>> = Vec::new();
    let mut tr: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            2 <= n <= 1000, 0 <= i <= n, bl.len() == i, tr.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] bl[k].len() == 2,
            forall|k: int| 0 <= k < i ==> #[trigger] tr[k].len() == 2,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < 2 ==> 1 <= #[trigger] bl[k][j] < tr[k][j] <= 10000000,
        decreases n - i,
    {
        let mut lower: Vec<i32> = Vec::new();
        let mut upper: Vec<i32> = Vec::new();
        let mut j = 0usize;
        while j < 2
            invariant
                0 <= j <= 2, lower.len() == j, upper.len() == j,
                forall|k: int| 0 <= k < j ==> 1 <= #[trigger] lower[k] < upper[k] <= 10000000,
            decreases 2 - j,
        {
            let lo = if i < raw_bl.len() && j < raw_bl[i].len() { raw_bl[i][j] } else { 1 };
            let hi = if i < raw_tr.len() && j < raw_tr[i].len() { raw_tr[i][j] } else { 2 };
            let lo = if lo < 1 { 1 } else if lo > 9999999 { 9999999 } else { lo };
            let hi = if hi <= lo { lo + 1 } else if hi > 10000000 { 10000000 } else { hi };
            lower.push(lo);
            upper.push(hi);
            j += 1;
        }
        bl.push(lower);
        tr.push(upper);
        i += 1;
    }
    (bl, tr)
}


pub fn generate_candidate(
    bl_x: &Vec<i32>,
    bl_y: &Vec<i32>,
    dx: &Vec<i32>,
    dy: &Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, Vec<Vec<i32>>))
    requires
        bl_x.len() == bl_y.len(),
        bl_x.len() == dx.len(),
        bl_x.len() == dy.len(),
        2 <= bl_x.len() <= 1_000,
        forall|i: int| 0 <= i < bl_x.len() ==> 0 <= #[trigger] bl_x[i],
        forall|i: int| 0 <= i < bl_y.len() ==> 0 <= #[trigger] bl_y[i],
        forall|i: int| 0 <= i < dx.len() ==> 1 <= #[trigger] dx[i],
        forall|i: int| 0 <= i < dy.len() ==> 1 <= #[trigger] dy[i],
        forall|i: int| 0 <= i < bl_x.len() ==> bl_x[i] as int + dx[i] as int <= 10_000_000,
        forall|i: int| 0 <= i < bl_y.len() ==> bl_y[i] as int + dy[i] as int <= 10_000_000,
    ensures
        result.0.len() == result.1.len(),
        2 <= result.0.len() <= 1_000,
        forall|i: int| 0 <= i < result.0.len() ==> result.0[i].len() == 2,
        forall|i: int| 0 <= i < result.1.len() ==> result.1[i].len() == 2,
        forall|i: int| 0 <= i < result.0.len() ==>
            result.0[i][0] < result.1[i][0] && result.0[i][1] < result.1[i][1],
        forall|i: int| 0 <= i < result.0.len() ==>
            0 <= #[trigger] result.0[i][0] <= 10_000_000 &&
            0 <= #[trigger] result.0[i][1] <= 10_000_000 &&
            0 <= #[trigger] result.1[i][0] <= 10_000_000 &&
            0 <= #[trigger] result.1[i][1] <= 10_000_000,
{
    let n = bl_x.len();
    // mutation 1: shrink by removing last rectangle (if n > 2)
    let limit: usize = if mutation_kind == 1 && n > 2 { (n - 1) as usize } else { n };

    let mut bl: Vec<Vec<i32>> = Vec::new();
    let mut tr: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;

    while k < limit
        invariant
            0 <= k <= limit,
            2 <= limit <= n,
            n == bl_x.len(),
            n == bl_y.len(),
            n == dx.len(),
            n == dy.len(),
            bl.len() == k,
            tr.len() == k,
            forall|j: int| 0 <= j < n as int ==> 0 <= #[trigger] bl_x[j],
            forall|j: int| 0 <= j < n as int ==> 0 <= #[trigger] bl_y[j],
            forall|j: int| 0 <= j < n as int ==> 1 <= #[trigger] dx[j],
            forall|j: int| 0 <= j < n as int ==> 1 <= #[trigger] dy[j],
            forall|j: int| 0 <= j < n as int ==> bl_x[j] as int + dx[j] as int <= 10_000_000,
            forall|j: int| 0 <= j < n as int ==> bl_y[j] as int + dy[j] as int <= 10_000_000,
            forall|j: int| 0 <= j < k as int ==> #[trigger] bl[j]@.len() == 2,
            forall|j: int| 0 <= j < k as int ==> #[trigger] tr[j]@.len() == 2,
            forall|j: int| 0 <= j < k as int ==>
                bl[j][0] < tr[j][0] && bl[j][1] < tr[j][1],
            forall|j: int| 0 <= j < k as int ==>
                0 <= #[trigger] bl[j][0] <= 10_000_000 &&
                0 <= #[trigger] bl[j][1] <= 10_000_000 &&
                0 <= #[trigger] tr[j][0] <= 10_000_000 &&
                0 <= #[trigger] tr[j][1] <= 10_000_000,
        decreases limit - k,
    {
        let bx = bl_x[k];
        let by = bl_y[k];
        let tx = bl_x[k] + dx[k];
        let ty = bl_y[k] + dy[k];

        let mut bl_pt: Vec<i32> = Vec::new();
        bl_pt.push(bx);
        bl_pt.push(by);
        assert(bl_pt@.len() == 2);
        assert(bl_pt[0] == bx);
        assert(bl_pt[1] == by);

        let mut tr_pt: Vec<i32> = Vec::new();
        tr_pt.push(tx);
        tr_pt.push(ty);
        assert(tr_pt@.len() == 2);
        assert(tr_pt[0] == tx);
        assert(tr_pt[1] == ty);

        assert(bx < tx);
        assert(by < ty);
        assert(0 <= bx <= 10_000_000);
        assert(0 <= by <= 10_000_000);
        assert(0 <= tx <= 10_000_000);
        assert(0 <= ty <= 10_000_000);

        bl.push(bl_pt);
        tr.push(tr_pt);

        k += 1;
    }

    (bl, tr)
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

fn random_rects(rng: &mut Rng, n: usize, coord_max: i32) -> (Vec<i32>, Vec<i32>, Vec<i32>, Vec<i32>) {
    let mut bl_x = Vec::with_capacity(n);
    let mut bl_y = Vec::with_capacity(n);
    let mut dx = Vec::with_capacity(n);
    let mut dy = Vec::with_capacity(n);

    for _ in 0..n {
        let bx = rng.gen_range_i64(0, coord_max as i64) as i32;
        let by = rng.gen_range_i64(0, coord_max as i64) as i32;
        let max_dx = 10_000_000 - bx;
        let max_dy = 10_000_000 - by;
        let width_cap = match rng.gen_range_usize(0, 2) {
            0 => 10.min(max_dx).max(1),
            1 => 1000.min(max_dx).max(1),
            _ => max_dx.max(1),
        };
        let height_cap = match rng.gen_range_usize(0, 2) {
            0 => 10.min(max_dy).max(1),
            1 => 1000.min(max_dy).max(1),
            _ => max_dy.max(1),
        };
        let d_x = rng.gen_range_i64(1, width_cap as i64) as i32;
        let d_y = rng.gen_range_i64(1, height_cap as i64) as i32;
        bl_x.push(bx);
        bl_y.push(by);
        dx.push(d_x);
        dy.push(d_y);
    }
    (bl_x, bl_y, dx, dy)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3047);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |bl: Vec<Vec<i32>>, tr: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    total: &mut usize| {
        let (bl, tr) = generate_test_case(bl, tr);
        if *total >= count { return; }
        let key = format!("{:?}{:?}", bl, tr);
        if !seen.insert(key) { return; }
        let output = Solution::largest_square_area(bl.clone(), tr.clone());
        writeln!(out, "{}", json!({
            "input": {"bl": bl, "tr": tr},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example 1: output 1
    emit(vec![vec![1,1],vec![2,2],vec![3,1]], vec![vec![3,3],vec![4,4],vec![6,6]],
         &mut seen, &mut out, &mut total);
    // Example 2: output 4
    emit(vec![vec![1,1],vec![1,3],vec![1,5]], vec![vec![5,5],vec![5,7],vec![5,9]],
         &mut seen, &mut out, &mut total);
    // Example 3: output 1
    emit(vec![vec![1,1],vec![2,2],vec![1,2]], vec![vec![3,3],vec![4,4],vec![3,4]],
         &mut seen, &mut out, &mut total);
    // Example 4: output 0 (no intersection)
    emit(vec![vec![1,1],vec![3,3],vec![3,1]], vec![vec![2,2],vec![4,4],vec![4,2]],
         &mut seen, &mut out, &mut total);

    // Edge cases
    // Two identical rectangles
    emit(vec![vec![0,0],vec![0,0]], vec![vec![5,5],vec![5,5]],
         &mut seen, &mut out, &mut total);
    // Two barely touching (no overlap)
    emit(vec![vec![0,0],vec![5,0]], vec![vec![5,5],vec![10,5]],
         &mut seen, &mut out, &mut total);
    // Two with minimal overlap
    emit(vec![vec![0,0],vec![4,4]], vec![vec![5,5],vec![6,6]],
         &mut seen, &mut out, &mut total);
    // Min boundary coordinates
    emit(vec![vec![0,0],vec![0,0]], vec![vec![1,1],vec![1,1]],
         &mut seen, &mut out, &mut total);
    // Max boundary coordinates
    emit(vec![vec![0,0],vec![9_999_999,9_999_999]],
         vec![vec![10_000_000,10_000_000],vec![10_000_000,10_000_000]],
         &mut seen, &mut out, &mut total);

    let mutation_kinds: Vec<u8> = vec![0, 1];

    // Generate via verified generator with diverse sizes and mutations
    for i in 0..80 {
        if total >= count { break; }
        let n = match i % 5 {
            0 => rng.gen_range_usize(2, 5),        // tiny
            1 => rng.gen_range_usize(2, 10),       // small
            2 => rng.gen_range_usize(11, 50),      // medium
            3 => rng.gen_range_usize(51, 200),     // large
            _ => rng.gen_range_usize(201, 1000),   // max
        };
        let coord_max = match i % 4 {
            0 => 100,              // small coords
            1 => 10_000,           // medium coords
            2 => 1_000_000,        // large coords
            _ => 9_999_999,        // max coords
        };
        let (bl_x, bl_y, dx_v, dy_v) = random_rects(&mut rng, n, coord_max);
        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let (bl, tr) = generate_candidate(&bl_x, &bl_y, &dx_v, &dy_v, mk);
        emit(bl, tr, &mut seen, &mut out, &mut total);
    }

    // Fill remaining with random inputs
    while total < count {
        let n = rng.gen_range_usize(2, 1000);
        let coord_max = rng.gen_range_i64(1, 9_999_999) as i32;
        let (bl_x, bl_y, dx_v, dy_v) = random_rects(&mut rng, n, coord_max);
        let mk = rng.gen_range_usize(0, 1) as u8;
        let (bl, tr) = generate_candidate(&bl_x, &bl_y, &dx_v, &dy_v, mk);
        emit(bl, tr, &mut seen, &mut out, &mut total);
    }
}
