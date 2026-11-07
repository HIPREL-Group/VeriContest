use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    row: usize,
    col: usize,
    value: i32,
) -> (result: (Vec<Vec<i32>>, usize, usize, i32))
    requires
        1 <= m <= 300,
        1 <= n <= 300,
        row < m,
        col < n,
    ensures
        ({
            let dp = result.0;
            let r = result.1;
            let c = result.2;
            let v = result.3;
            &&& 1 <= dp.len() <= 300
            &&& dp.len() == m
            &&& forall|i: int| 0 <= i < dp.len() ==> (#[trigger] dp[i]).len() == n
            &&& forall|i: int| 0 <= i < dp.len() ==> 1 <= (#[trigger] dp[i]).len() <= 300
            &&& forall|i: int, j: int| 0 <= i < dp.len() && 0 <= j < dp[0].len()
                ==> (#[trigger] dp[i][j] == 0 || dp[i][j] == 1)
            &&& r < dp.len()
            &&& c < dp[r as int].len()
            &&& v == value
        }),
{
    let mut dp: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            0 <= i <= m,
            dp.len() == i,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] dp[k]).len() == n,
            forall|k: int| 0 <= k < i as int ==> 1 <= (#[trigger] dp[k]).len() <= 300,
            forall|k: int, j: int| 0 <= k < i as int && 0 <= j < n as int
                ==> (#[trigger] dp[k][j]) == 0,
            1 <= n <= 300,
        decreases m - i,
    {
        let mut row_vec: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                row_vec.len() == j,
                forall|k: int| 0 <= k < j as int ==> (#[trigger] row_vec[k]) == 0,
            decreases n - j,
        {
            row_vec.push(0);
            j = j + 1;
        }
        dp.push(row_vec);
        i = i + 1;
    }

    proof {
        assert(dp.len() == m);
        assert(forall|k: int| 0 <= k < dp.len() ==> (#[trigger] dp[k]).len() == n);
        assert(dp[0int].len() == n);
    }

    (dp, row, col, value)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn print_json(matrix: &Vec<Vec<i32>>) {
    print!("{{\"matrix\":[");
    for i in 0..matrix.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..matrix[i].len() {
            if j > 0 { print!(","); }
            print!("{}", matrix[i][j]);
        }
        print!("]");
    }
    println!("]}}");
}

fn pick_dims(rng: &mut Rng, mode: usize, t: usize) -> (usize, usize) {
    match mode {
        0 => (1, 1),
        1 => (1, 300),
        2 => (300, 1),
        3 => (300, 300),
        4 => (2, 2),
        5 => (rng.gen_range_usize(1, 10), rng.gen_range_usize(1, 10)),
        6 => (rng.gen_range_usize(1, 50), rng.gen_range_usize(1, 50)),
        7 => (rng.gen_range_usize(100, 300), rng.gen_range_usize(100, 300)),
        8 => (rng.gen_range_usize(1, 300), 1),
        9 => (1, rng.gen_range_usize(1, 300)),
        _ => {
            let m = 1 + (t % 300);
            let n = 1 + ((t * 7) % 300);
            (m, n)
        }
    }
}

fn pick_indices(rng: &mut Rng, mode: usize, m: usize, n: usize) -> (usize, usize) {
    match mode % 5 {
        0 => (0, 0),
        1 => (m - 1, n - 1),
        2 => (0, n - 1),
        3 => (m - 1, 0),
        _ => (rng.gen_range_usize(0, m - 1), rng.gen_range_usize(0, n - 1)),
    }
}

fn pick_value(rng: &mut Rng, mode: usize) -> i32 {
    match mode % 6 {
        0 => 0,
        1 => 1,
        2 => i32::MAX,
        3 => i32::MIN,
        4 => -1,
        _ => {
            let v = (rng.next_u64() % 10) as i32;
            v
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (m, n) = pick_dims(&mut rng, mode, t);
        let (row, col) = pick_indices(&mut rng, t, m, n);
        let value = pick_value(&mut rng, t);
        let (dp, _r, _c, _v) = generate_test_case(m, n, row, col, value);
        print_json(&dp);
    }
}