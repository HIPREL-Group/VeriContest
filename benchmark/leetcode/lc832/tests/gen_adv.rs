use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, bits: &Vec<Vec<i32>>) -> (image: Vec<Vec<i32>>)
    requires
        1 <= n <= 20,
        bits.len() == n,
        forall |i: int| 0 <= i < bits.len() ==> #[trigger] bits[i].len() == n,
        forall |i: int, j: int| 0 <= i < bits.len() && 0 <= j < bits[i].len() ==> 0 <= #[trigger] bits[i][j] <= 1,
    ensures
        1 <= image.len() <= 20,
        image.len() == n,
        forall |i: int| 0 <= i < image.len() ==> #[trigger] image[i].len() == image.len(),
        forall |i: int, j: int| 0 <= i < image.len() && 0 <= j < image[i].len() ==> 0 <= #[trigger] image[i][j] <= 1,
{
    let mut image: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            1 <= n <= 20,
            bits.len() == n,
            0 <= i <= n,
            image.len() == i,
            forall |k: int| 0 <= k < bits.len() ==> #[trigger] bits[k].len() == n,
            forall |k: int, j: int| 0 <= k < bits.len() && 0 <= j < bits[k].len() ==> 0 <= #[trigger] bits[k][j] <= 1,
            forall |k: int| 0 <= k < image.len() ==> #[trigger] image[k].len() == n,
            forall |k: int, j: int| 0 <= k < image.len() && 0 <= j < image[k].len() ==> 0 <= #[trigger] image[k][j] <= 1,
        decreases n - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                1 <= n <= 20,
                bits.len() == n,
                i < n,
                0 <= j <= n,
                row.len() == j,
                bits[i as int].len() == n,
                forall |k: int, m: int| 0 <= k < bits.len() && 0 <= m < bits[k].len() ==> 0 <= #[trigger] bits[k][m] <= 1,
                forall |m: int| 0 <= m < row.len() ==> 0 <= #[trigger] row[m] <= 1,
            decreases n - j,
        {
            let v = bits[i][j];
            let b: i32 = if v == 0 { 0 } else { 1 };
            row.push(b);
            j = j + 1;
        }
        image.push(row);
        i = i + 1;
    }
    image
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
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
    fn gen_bit(&mut self) -> i32 {
        (self.next_u64() % 2) as i32
    }
}

fn make_bits(rng: &mut Rng, mode: usize, n: usize) -> Vec<Vec<i32>> {
    let mut bits: Vec<Vec<i32>> = Vec::new();
    for i in 0..n {
        let mut row: Vec<i32> = Vec::new();
        for j in 0..n {
            let v: i32 = match mode {
                0 => rng.gen_bit(),
                1 => 0,
                2 => 1,
                3 => if j < n / 2 { 0 } else { 1 },
                4 => if j < n / 2 { 1 } else { 0 },
                5 => if (i + j) % 2 == 0 { 0 } else { 1 },
                6 => if i == j { 1 } else { 0 },
                7 => if i + j == n - 1 { 1 } else { 0 },
                8 => if j == 0 || j == n - 1 { 1 } else { 0 },
                9 => if i == 0 || i == n - 1 || j == 0 || j == n - 1 { 1 } else { 0 },
                _ => rng.gen_bit(),
            };
            row.push(v);
        }
        bits.push(row);
    }
    bits
}

fn print_json(image: &Vec<Vec<i32>>) {
    print!("{{\"image\":[");
    for i in 0..image.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..image[i].len() {
            if j > 0 { print!(","); }
            print!("{}", image[i][j]);
        }
        print!("]");
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match t % 7 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 20,
            4 => 10,
            5 => rng.gen_range_usize(1, 20),
            _ => rng.gen_range_usize(1, 20),
        };
        let bits = make_bits(&mut rng, mode, n);
        let image = generate_test_case(n, &bits);
        print_json(&image);
    }
}