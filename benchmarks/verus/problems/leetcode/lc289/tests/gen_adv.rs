use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    bits: &Vec<Vec<i32>>,
    row: usize,
    col: usize,
    value: i32,
) -> (result: (Vec<Vec<i32>>, usize, usize, i32))
    requires
        1 <= m <= 25,
        1 <= n <= 25,
        bits.len() == m,
        forall|i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i]).len() == n,
        forall|i: int, j: int| 0 <= i < bits.len() && 0 <= j < bits[i].len()
            ==> (#[trigger] bits[i][j] == 0 || bits[i][j] == 1),
        row < m,
        col < n,
        value == 0 || value == 1,
    ensures
        ({
            let board = result.0;
            &&& 1 <= board.len() <= 25
            &&& board.len() == m
            &&& 1 <= board[0].len() <= 25
            &&& board[0].len() == n
            &&& (forall|r: int| 0 <= r < board.len() ==> (#[trigger] board[r]).len() == board[0].len())
            &&& (forall|r: int, c: int|
                    0 <= r < board.len() && 0 <= c < board[r].len()
                    ==> (#[trigger] board[r][c] == 0 || board[r][c] == 1))
            &&& result.1 < board.len()
            &&& result.2 < board[0].len()
            &&& (result.3 == 0 || result.3 == 1)
        }),
{
    let mut board: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            0 <= i <= m,
            board.len() == i,
            1 <= m <= 25,
            1 <= n <= 25,
            bits.len() == m,
            forall|k: int| 0 <= k < bits.len() ==> (#[trigger] bits[k]).len() == n,
            forall|k: int, j: int| 0 <= k < bits.len() && 0 <= j < bits[k].len()
                ==> (#[trigger] bits[k][j] == 0 || bits[k][j] == 1),
            forall|k: int| 0 <= k < board.len() ==> (#[trigger] board[k]).len() == n,
            forall|k: int, j: int| 0 <= k < board.len() && 0 <= j < board[k].len()
                ==> (#[trigger] board[k][j] == 0 || board[k][j] == 1),
        decreases m - i,
    {
        let mut row_vec: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        assert(bits[i as int].len() == n);
        while j < n
            invariant
                0 <= j <= n,
                row_vec.len() == j,
                i < m,
                bits.len() == m,
                bits[i as int].len() == n,
                forall|k: int, jj: int| 0 <= k < bits.len() && 0 <= jj < bits[k].len()
                    ==> (#[trigger] bits[k][jj] == 0 || bits[k][jj] == 1),
                forall|jj: int| 0 <= jj < row_vec.len()
                    ==> (#[trigger] row_vec[jj] == 0 || row_vec[jj] == 1),
            decreases n - j,
        {
            assert(j < bits[i as int].len());
            let v = bits[i][j];
            assert(v == 0 || v == 1);
            row_vec.push(v);
            j = j + 1;
        }
        assert(row_vec.len() == n);
        board.push(row_vec);
        i = i + 1;
    }

    assert(board.len() == m);
    assert(board[0int].len() == n);

    (board, row, col, value)
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
    fn gen_bit(&mut self) -> i32 {
        (self.next_u64() & 1) as i32
    }
}

fn make_bits(m: usize, n: usize, mode: usize, rng: &mut Rng) -> Vec<Vec<i32>> {
    let mut bits: Vec<Vec<i32>> = Vec::with_capacity(m);
    for i in 0..m {
        let mut row: Vec<i32> = Vec::with_capacity(n);
        for j in 0..n {
            let v = match mode {
                0 => 0i32,
                1 => 1i32,
                2 => rng.gen_bit(),
                3 => if (i + j) % 2 == 0 { 1 } else { 0 },
                4 => if i == 0 || i + 1 == m || j == 0 || j + 1 == n { 1 } else { 0 },
                5 => if i == m / 2 { 1 } else { 0 },
                6 => if j == n / 2 { 1 } else { 0 },
                7 => {
                    // blinker: three in a row near top
                    if i == 0 && j < 3 && j < n { 1 } else { 0 }
                }
                8 => {
                    // block
                    if i < 2 && j < 2 { 1 } else { 0 }
                }
                9 => {
                    // random sparse
                    if rng.next_u64() % 5 == 0 { 1 } else { 0 }
                }
                _ => rng.gen_bit(),
            };
            row.push(v);
        }
        bits.push(row);
    }
    bits
}

fn print_json(board: &Vec<Vec<i32>>, row: usize, col: usize, value: i32) {
    print!("{{\"board\":[");
    for i in 0..board.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..board[i].len() {
            if j > 0 { print!(","); }
            print!("{}", board[i][j]);
        }
        print!("]");
    }
    println!("],\"row\":{},\"col\":{},\"value\":{}}}", row, col, value);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let m = match mode {
            0 => 1,
            1 => 25,
            2 => rng.gen_range_usize(1, 25),
            3 => rng.gen_range_usize(2, 10),
            4 => rng.gen_range_usize(3, 25),
            5 => rng.gen_range_usize(1, 25),
            6 => rng.gen_range_usize(1, 25),
            7 => rng.gen_range_usize(3, 25),
            8 => rng.gen_range_usize(2, 25),
            9 => rng.gen_range_usize(1, 25),
            _ => rng.gen_range_usize(1, 25),
        };
        let n = match mode {
            0 => 1,
            1 => 25,
            2 => rng.gen_range_usize(1, 25),
            3 => rng.gen_range_usize(2, 10),
            4 => rng.gen_range_usize(3, 25),
            5 => rng.gen_range_usize(1, 25),
            6 => rng.gen_range_usize(1, 25),
            7 => rng.gen_range_usize(3, 25),
            8 => rng.gen_range_usize(2, 25),
            9 => rng.gen_range_usize(1, 25),
            _ => rng.gen_range_usize(1, 25),
        };

        let bits = make_bits(m, n, mode, &mut rng);
        let row = rng.gen_range_usize(0, m - 1);
        let col = rng.gen_range_usize(0, n - 1);
        let value = rng.gen_bit();

        let (board, r, c, v) = generate_test_case(m, n, &bits, row, col, value);
        print_json(&board, r, c, v);
    }
}