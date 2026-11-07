use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    bits: &Vec<Vec<i32>>,
) -> (mat: Vec<Vec<i32>>)
    requires
        1 <= m <= 100,
        1 <= n <= 100,
        bits.len() == m,
        forall|i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i]).len() == n,
        forall|i: int, j: int| 0 <= i < bits.len() && 0 <= j < bits[i].len() ==>
            #[trigger] bits[i][j] == 0 || bits[i][j] == 1,
    ensures
        1 <= mat.len() <= 100,
        forall|r: int| 0 <= r < mat.len() ==> 1 <= (#[trigger] mat[r]).len() <= 100,
        forall|r: int| 0 <= r < mat.len() ==> (#[trigger] mat[r]).len() == mat[0].len(),
        forall|r: int, c: int| 0 <= r < mat.len() && 0 <= c < mat[r].len() ==>
            #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
{
    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            1 <= m <= 100,
            1 <= n <= 100,
            bits.len() == m,
            forall|a: int| 0 <= a < bits.len() ==> (#[trigger] bits[a]).len() == n,
            forall|a: int, b: int| 0 <= a < bits.len() && 0 <= b < bits[a].len() ==>
                #[trigger] bits[a][b] == 0 || bits[a][b] == 1,
            0 <= i <= m,
            mat.len() == i,
            forall|a: int| 0 <= a < mat.len() ==> (#[trigger] mat[a]).len() == n,
            forall|a: int, b: int| 0 <= a < mat.len() && 0 <= b < mat[a].len() ==>
                #[trigger] mat[a][b] == 0 || mat[a][b] == 1,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                1 <= n <= 100,
                0 <= j <= n,
                row.len() == j,
                i < bits.len(),
                bits[i as int].len() == n,
                forall|b: int| 0 <= b < bits[i as int].len() ==>
                    #[trigger] bits[i as int][b] == 0 || bits[i as int][b] == 1,
                forall|b: int| 0 <= b < row.len() ==>
                    #[trigger] row[b] == bits[i as int][b],
            decreases n - j,
        {
            row.push(bits[i][j]);
            j = j + 1;
        }
        assert(row.len() == n);
        assert(forall|b: int| 0 <= b < row.len() ==> #[trigger] row[b] == 0 || row[b] == 1);
        mat.push(row);
        i = i + 1;
    }
    assert(mat.len() == m);
    if m >= 1 {
        assert(mat[0].len() == n);
    }
    mat
}

}

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(1) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn build_bits(m: usize, n: usize, fill: &dyn Fn(usize, usize) -> i32) -> Vec<Vec<i32>> {
    let mut bits: Vec<Vec<i32>> = Vec::new();
    for i in 0..m {
        let mut row: Vec<i32> = Vec::new();
        for j in 0..n {
            let v = fill(i, j);
            row.push(if v == 1 { 1 } else { 0 });
        }
        bits.push(row);
    }
    bits
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

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<Vec<i32>> {
    match mode {
        0 => {
            // 1x1 all zero
            build_bits(1, 1, &|_i, _j| 0)
        }
        1 => {
            // 1x1 single one
            build_bits(1, 1, &|_i, _j| 1)
        }
        2 => {
            // identity matrix (all positions special)
            let n = 2 + (t % 10);
            let nn = n;
            build_bits(n, nn, &move |i, j| if i == j { 1 } else { 0 })
        }
        3 => {
            // all ones (no special)
            let m = 1 + (t % 10);
            let n = 1 + ((t * 3) % 10);
            build_bits(m, n, &|_i, _j| 1)
        }
        4 => {
            // all zeros
            let m = 1 + (t % 8);
            let n = 1 + ((t * 5) % 8);
            build_bits(m, n, &|_i, _j| 0)
        }
        5 => {
            // single 1 in middle
            let m = 3 + (t % 5);
            let n = 3 + (t % 5);
            let ci = m / 2;
            let cj = n / 2;
            build_bits(m, n, &move |i, j| if i == ci && j == cj { 1 } else { 0 })
        }
        6 => {
            // max size 100x100 identity-like
            build_bits(100, 100, &|i, j| if i == j { 1 } else { 0 })
        }
        7 => {
            // max size 100x100 random sparse
            let mut bits: Vec<Vec<i32>> = Vec::new();
            for _i in 0..100 {
                let mut row = Vec::new();
                for _j in 0..100 {
                    let v = if rng.next_u64() % 20 == 0 { 1 } else { 0 };
                    row.push(v);
                }
                bits.push(row);
            }
            bits
        }
        8 => {
            // 1 row
            let n = rng.gen_range(1, 100);
            let mut row = Vec::new();
            for _j in 0..n {
                row.push((rng.next_u64() % 2) as i32);
            }
            let mut bits = Vec::new();
            bits.push(row);
            bits
        }
        9 => {
            // 1 column
            let m = rng.gen_range(1, 100);
            let mut bits = Vec::new();
            for _i in 0..m {
                let mut row = Vec::new();
                row.push((rng.next_u64() % 2) as i32);
                bits.push(row);
            }
            bits
        }
        10 => {
            // one row all ones, one col all ones pattern
            let m = 4 + (t % 6);
            let n = 4 + (t % 6);
            build_bits(m, n, &move |i, j| if i == 0 || j == 0 { 1 } else { 0 })
        }
        _ => {
            // random
            let m = rng.gen_range(1, 20);
            let n = rng.gen_range(1, 20);
            let mut bits = Vec::new();
            for _i in 0..m {
                let mut row = Vec::new();
                for _j in 0..n {
                    row.push((rng.next_u64() % 2) as i32);
                }
                bits.push(row);
            }
            bits
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 12usize;
    let total = 200usize;

    for t in 0..total {
        let mode = if t < modes * 4 { t % modes } else { 11 };
        let bits = gen_mode(&mut rng, mode, t);
        let m = bits.len();
        let n = if m > 0 { bits[0].len() } else { 1 };
        if m == 0 || m > 100 || n == 0 || n > 100 { continue; }
        // verify all rows same length and values 0/1
        let mut ok = true;
        for r in &bits {
            if r.len() != n { ok = false; break; }
            for &v in r {
                if v != 0 && v != 1 { ok = false; break; }
            }
            if !ok { break; }
        }
        if !ok { continue; }
        let mat = generate_test_case(m, n, &bits);
        print_json(&mat);
    }
}