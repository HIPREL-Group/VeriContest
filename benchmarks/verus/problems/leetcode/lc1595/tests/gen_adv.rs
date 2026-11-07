use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    flat: &Vec<i32>,
) -> (cost: Vec<Vec<i32>>)
    requires
        1 <= n <= 12,
        n <= m <= 12,
        flat.len() == m * n,
        forall|k: int| 0 <= k < flat.len() ==> 0 <= #[trigger] flat[k] <= 100,
    ensures
        1 <= cost.len() <= 12,
        cost.len() == m,
        cost[0]@.len() == n,
        forall|i: int| 0 <= i < cost.len() ==> (#[trigger] cost[i])@.len() == cost[0]@.len(),
        1 <= cost[0]@.len() <= 12,
        cost.len() >= cost[0]@.len(),
        forall|i: int, j: int|
            #![trigger cost[i]@[j]]
            0 <= i < cost.len() && 0 <= j < cost[0]@.len()
                ==> 0 <= cost[i]@[j] <= 100,
{
    let mut cost: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < m
        invariant
            1 <= n <= 12,
            n <= m <= 12,
            flat.len() == m * n,
            forall|k: int| 0 <= k < flat.len() ==> 0 <= #[trigger] flat[k] <= 100,
            0 <= i <= m,
            cost.len() == i,
            forall|ii: int| 0 <= ii < i as int ==> (#[trigger] cost[ii])@.len() == n as int,
            forall|ii: int, jj: int|
                #![trigger cost[ii]@[jj]]
                0 <= ii < i as int && 0 <= jj < n as int
                    ==> 0 <= cost[ii]@[jj] <= 100,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;

        proof {
            assert(i < m);
            assert(i + 1 <= m);
            assert((i + 1) * n <= m * n) by (nonlinear_arith)
                requires i + 1 <= m, n >= 0;
            assert(i * n + n == (i + 1) * n) by (nonlinear_arith);
            assert(i * n <= m * n) by (nonlinear_arith)
                requires i <= m, n >= 0;
        }
        let base: usize = i * n;

        while j < n
            invariant
                1 <= n <= 12,
                n <= m <= 12,
                i < m,
                flat.len() == m * n,
                forall|k: int| 0 <= k < flat.len() ==> 0 <= #[trigger] flat[k] <= 100,
                0 <= j <= n,
                row.len() == j,
                base == i * n,
                base + n <= flat.len(),
                forall|jj: int| 0 <= jj < j as int ==>
                    #[trigger] row[jj] == flat[base as int + jj]
                    && 0 <= row[jj] <= 100,
            decreases n - j,
        {
            let v = flat[base + j];
            assert(0 <= v <= 100);
            row.push(v);
            j = j + 1;
        }

        assert(row@.len() == n as int);
        cost.push(row);
        i = i + 1;
    }

    assert(cost.len() == m);
    assert(cost[0]@.len() == n as int);

    cost
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
        self.state = self
            .state
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
        let v = (self.next_u64() % span) as i32;
        lo + v
    }
}

fn make_flat(rng: &mut Rng, m: usize, n: usize, mode: usize) -> Vec<i32> {
    let total = m * n;
    let mut v: Vec<i32> = Vec::with_capacity(total);
    for k in 0..total {
        let x: i32 = match mode {
            0 => rng.gen_range_i32(0, 100),
            1 => 0,
            2 => 100,
            3 => if (k / n + k % n) % 2 == 0 { 0 } else { 100 },
            4 => {
                // diagonal cheap
                let i = k / n;
                let j = k % n;
                if i == j { 0 } else { 100 }
            }
            5 => {
                // single cheap column
                if k % n == 0 { rng.gen_range_i32(0, 5) } else { rng.gen_range_i32(50, 100) }
            }
            6 => {
                // single cheap row
                if k / n == 0 { rng.gen_range_i32(0, 5) } else { rng.gen_range_i32(50, 100) }
            }
            7 => rng.gen_range_i32(0, 10),
            8 => rng.gen_range_i32(90, 100),
            9 => {
                let i = (k / n) as i32;
                let j = (k % n) as i32;
                let d = (i - j).abs();
                (d * 5).min(100)
            }
            _ => rng.gen_range_i32(0, 100),
        };
        let xc = if x < 0 { 0 } else if x > 100 { 100 } else { x };
        v.push(xc);
    }
    v
}

fn print_json(cost: &Vec<Vec<i32>>) {
    print!("{{\"cost\":[");
    for i in 0..cost.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..cost[i].len() {
            if j > 0 { print!(","); }
            print!("{}", cost[i][j]);
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

    // Include some fixed edge cases
    let fixed: Vec<(usize, usize, usize)> = vec![
        (1, 1, 0),
        (1, 1, 1),
        (1, 1, 2),
        (2, 1, 0),
        (2, 2, 0),
        (12, 12, 0),
        (12, 12, 1),
        (12, 12, 2),
        (12, 1, 0),
        (12, 12, 3),
        (12, 12, 4),
        (12, 12, 5),
        (12, 12, 6),
        (6, 6, 9),
        (12, 6, 9),
    ];

    let mut emitted = 0usize;
    for &(m, n, mode) in fixed.iter() {
        let flat = make_flat(&mut rng, m, n, mode);
        let cost = generate_test_case(m, n, &flat);
        print_json(&cost);
        emitted += 1;
    }

    while emitted < total {
        let mode = rng.gen_range_usize(0, modes - 1);
        let m = rng.gen_range_usize(1, 12);
        let n = rng.gen_range_usize(1, m);
        let flat = make_flat(&mut rng, m, n, mode);
        let cost = generate_test_case(m, n, &flat);
        print_json(&cost);
        emitted += 1;
    }
}