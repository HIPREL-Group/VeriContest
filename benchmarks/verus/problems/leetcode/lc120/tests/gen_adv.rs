use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    num_rows: usize,
    values: &Vec<Vec<i32>>,
) -> (triangle: Vec<Vec<i32>>)
    requires
        1 <= num_rows <= 200,
        values.len() == num_rows,
        forall |row: int| 0 <= row < values.len() ==> #[trigger] values[row].len() == row + 1,
        forall |row: int, col: int|
            0 <= row < values.len() && 0 <= col < values[row].len() ==> -10000 <= #[trigger] values[row][col] <= 10000,
    ensures
        1 <= triangle.len() <= 200,
        triangle[0].len() == 1,
        forall |row: int| 0 <= row < triangle.len() ==> #[trigger] triangle[row].len() == row + 1,
        forall |row: int, col: int|
            0 <= row < triangle.len() && 0 <= col < triangle[row].len() ==> -10000 <= #[trigger] triangle[row][col] <= 10000,
{
    let mut triangle: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < num_rows
        invariant
            1 <= num_rows <= 200,
            values.len() == num_rows,
            0 <= r <= num_rows,
            triangle.len() == r,
            forall |row: int| 0 <= row < values.len() ==> #[trigger] values[row].len() == row + 1,
            forall |row: int, col: int|
                0 <= row < values.len() && 0 <= col < values[row].len() ==> -10000 <= #[trigger] values[row][col] <= 10000,
            forall |row: int| 0 <= row < triangle.len() ==> #[trigger] triangle[row].len() == row + 1,
            forall |row: int, col: int|
                0 <= row < triangle.len() && 0 <= col < triangle[row].len() ==> -10000 <= #[trigger] triangle[row][col] <= 10000,
        decreases num_rows - r,
    {
        let mut row_vec: Vec<i32> = Vec::new();
        let expected_len: usize = r + 1;
        let mut c: usize = 0;
        while c < expected_len
            invariant
                0 <= c <= expected_len,
                expected_len == r + 1,
                r < num_rows,
                values.len() == num_rows,
                row_vec.len() == c,
                values[r as int].len() == r + 1,
                forall |col: int| 0 <= col < row_vec.len() ==> -10000 <= #[trigger] row_vec[col] <= 10000,
                forall |row: int, col: int|
                    0 <= row < values.len() && 0 <= col < values[row].len() ==> -10000 <= #[trigger] values[row][col] <= 10000,
            decreases expected_len - c,
        {
            assert(c < values[r as int].len());
            assert(-10000 <= values[r as int][c as int] <= 10000);
            let v = values[r][c];
            row_vec.push(v);
            c += 1;
        }
        assert(row_vec.len() == r + 1);
        triangle.push(row_vec);
        assert(triangle[r as int].len() == r + 1);
        r += 1;
    }
    triangle
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        (lo as i64 + v as i64) as i32
    }
}

fn build_values(rng: &mut Rng, num_rows: usize, mode: usize) -> Vec<Vec<i32>> {
    let mut v: Vec<Vec<i32>> = Vec::with_capacity(num_rows);
    for r in 0..num_rows {
        let mut row = Vec::with_capacity(r + 1);
        for _c in 0..(r + 1) {
            let val = match mode {
                0 => rng.gen_range_i32(-10000, 10000),
                1 => 0,
                2 => 10000,
                3 => -10000,
                4 => 1,
                5 => -1,
                6 => if rng.next_u64() % 2 == 0 { 10000 } else { -10000 },
                7 => rng.gen_range_i32(-10, 10),
                8 => rng.gen_range_i32(-100, 100),
                9 => if rng.next_u64() % 3 == 0 { 10000 } else if rng.next_u64() % 3 == 1 { -10000 } else { 0 },
                _ => rng.gen_range_i32(-10000, 10000),
            };
            row.push(val);
        }
        v.push(row);
    }
    v
}

fn print_json(triangle: &[Vec<i32>]) {
    print!("{{\"triangle\":[");
    for i in 0..triangle.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..triangle[i].len() {
            if j > 0 { print!(","); }
            print!("{}", triangle[i][j]);
        }
        print!("]");
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let num_rows: usize = match mode {
            0 => 1,
            1 => 200,
            2 => 2,
            3 => 3,
            4 => 200,
            5 => rng.gen_range_usize(1, 200),
            6 => rng.gen_range_usize(1, 50),
            7 => rng.gen_range_usize(50, 200),
            8 => rng.gen_range_usize(1, 200),
            _ => rng.gen_range_usize(1, 200),
        };
        let values = build_values(&mut rng, num_rows, mode);
        let triangle = generate_test_case(num_rows, &values);
        print_json(&triangle);
    }
}