use vstd::prelude::*;

verus! {

pub fn generate_test_case(m: usize, n: usize) -> (mat: Vec<Vec<i32>>)
    requires
        1 <= m <= 500,
        1 <= n <= 500,
    ensures
        1 <= mat.len() <= 500,
        forall |i: int| 0 <= i < mat.len() ==> 1 <= #[trigger] mat[i].len() <= 500,
        forall |i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() == mat[0].len(),
        forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[0].len() ==> 1 <= #[trigger] mat[i][j] <= 100_000,
        forall |i: int, j: int|
            0 <= i && i + 1 < mat.len() && 0 <= j < mat[0].len() ==> #[trigger] mat[i][j] != mat[i + 1][j],
        forall |i: int, j: int|
            0 <= i < mat.len() && 0 <= j && j + 1 < mat[0].len() ==> #[trigger] mat[i][j] != mat[i][j + 1],
{
    let mut row: Vec<i32> = Vec::new();
    row.push(1);
    let mut mat: Vec<Vec<i32>> = Vec::new();
    mat.push(row);
    mat
}

} // verus!

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn print_json(mat: &Vec<Vec<i32>>) {
    print!("{{\"mat\":[");
    for i in 0..mat.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..mat[i].len() {
            if j > 0 { print!(","); }
            print!("{}", mat[i][j]);
        }
        print!("]");
    }
    println!("]}}");
}

fn pick_dims(rng: &mut Rng, mode: usize, t: usize) -> (usize, usize) {
    match mode {
        0 => (1, 1),
        1 => (1, rng.gen_range(1, 500)),
        2 => (rng.gen_range(1, 500), 1),
        3 => (500, 500),
        4 => (500, rng.gen_range(1, 500)),
        5 => (rng.gen_range(1, 500), 500),
        6 => (2, 2),
        7 => (rng.gen_range(2, 10), rng.gen_range(2, 10)),
        8 => (rng.gen_range(50, 100), rng.gen_range(50, 100)),
        9 => (rng.gen_range(1, 20), rng.gen_range(1, 20)),
        _ => {
            let m = 1 + (t % 500);
            let n = 1 + ((t * 7) % 500);
            (m, n)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let (m, n) = pick_dims(&mut rng, mode, t);
        let mat = generate_test_case(m, n);
        print_json(&mat);
    }
}
