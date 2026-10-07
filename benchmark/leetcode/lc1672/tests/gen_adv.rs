use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    values: &Vec<Vec<i32>>,
) -> (accounts: Vec<Vec<i32>>)
    requires
        1 <= m <= 50,
        1 <= n <= 50,
        values.len() == m,
        forall|i: int| 0 <= i < values.len() ==> #[trigger] values[i].len() == n,
        forall|i: int, j: int|
            0 <= i < values.len() && 0 <= j < values[i].len()
                ==> 1 <= #[trigger] values[i][j] <= 100,
    ensures
        1 <= accounts.len() <= 50,
        1 <= accounts[0].len() <= 50,
        forall|i: int|
            0 <= i < accounts.len()
                ==> #[trigger] accounts[i].len() == accounts[0].len(),
        forall|i: int, j: int|
            0 <= i < accounts.len() && 0 <= j < accounts[i].len()
                ==> 1 <= #[trigger] accounts[i][j] <= 100,
{
    let mut accounts: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            0 <= i <= m,
            1 <= m <= 50,
            1 <= n <= 50,
            values.len() == m,
            accounts.len() == i,
            forall|k: int| 0 <= k < values.len() ==> #[trigger] values[k].len() == n,
            forall|k: int, j: int|
                0 <= k < values.len() && 0 <= j < values[k].len()
                    ==> 1 <= #[trigger] values[k][j] <= 100,
            forall|k: int| 0 <= k < accounts.len() ==> #[trigger] accounts[k].len() == n,
            forall|k: int, j: int|
                0 <= k < accounts.len() && 0 <= j < accounts[k].len()
                    ==> 1 <= #[trigger] accounts[k][j] <= 100,
        decreases m - i,
    {
        let row_src: &Vec<i32> = &values[i];
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                1 <= n <= 50,
                row.len() == j,
                row_src.len() == n,
                i < values.len(),
                row_src@ == values[i as int]@,
                forall|t: int| 0 <= t < values[i as int].len() ==>
                    1 <= #[trigger] values[i as int][t] <= 100,
                forall|t: int| 0 <= t < row.len() ==> 1 <= #[trigger] row[t] <= 100,
            decreases n - j,
        {
            let v: i32 = row_src[j];
            assert(1 <= v <= 100);
            row.push(v);
            j = j + 1;
        }
        accounts.push(row);
        i = i + 1;
    }
    assert(accounts.len() == m);
    assert(accounts[0].len() == n);
    accounts
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_values(rng: &mut Rng, m: usize, n: usize, mode: usize) -> Vec<Vec<i32>> {
    let mut v = Vec::with_capacity(m);
    for i in 0..m {
        let mut row = Vec::with_capacity(n);
        for j in 0..n {
            let val: i32 = match mode {
                0 => rng.gen_range_i32(1, 100),
                1 => 1,
                2 => 100,
                3 => if (i + j) % 2 == 0 { 1 } else { 100 },
                4 => if i == 0 { 100 } else { 1 },
                5 => if i == m - 1 { 100 } else { 1 },
                6 => if j == 0 { 100 } else { 1 },
                7 => ((i * n + j) as i32 % 100) + 1,
                8 => rng.gen_range_i32(1, 10),
                9 => rng.gen_range_i32(90, 100),
                _ => rng.gen_range_i32(1, 100),
            };
            row.push(val);
        }
        v.push(row);
    }
    v
}

fn print_json(accounts: &Vec<Vec<i32>>) {
    print!("{{\"accounts\":[");
    for i in 0..accounts.len() {
        if i > 0 {
            print!(",");
        }
        print!("[");
        for j in 0..accounts[i].len() {
            if j > 0 {
                print!(",");
            }
            print!("{}", accounts[i][j]);
        }
        print!("]");
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (m, n) = match mode {
            0 => (rng.gen_range_usize(1, 50), rng.gen_range_usize(1, 50)),
            1 => (1, 1),
            2 => (50, 50),
            3 => (1, 50),
            4 => (50, 1),
            5 => (rng.gen_range_usize(2, 10), rng.gen_range_usize(2, 10)),
            6 => (3, 3),
            7 => (rng.gen_range_usize(1, 20), rng.gen_range_usize(1, 20)),
            8 => (rng.gen_range_usize(5, 50), rng.gen_range_usize(5, 50)),
            9 => (rng.gen_range_usize(1, 50), rng.gen_range_usize(1, 50)),
            _ => (2, 2),
        };

        let values = build_values(&mut rng, m, n, mode);
        let accounts = generate_test_case(m, n, &values);
        print_json(&accounts);
    }
}