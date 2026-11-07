use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    values: &Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= n <= 300,
        values.len() == n * n,
        forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 4_000_000i32,
    ensures
        1 <= result.len() <= 300,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == result.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 1 <= #[trigger] result[i][j] <= 4_000_000i32,
{
    let mut matrix: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < n
        invariant
            0 <= r <= n,
            1 <= n <= 300,
            matrix.len() == r as int,
            values.len() == n * n,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 4_000_000i32,
            forall|i: int| 0 <= i < r ==> (#[trigger] matrix[i]).len() == n,
            forall|i: int, j: int|
                0 <= i < r && 0 <= j < n ==>
                1 <= #[trigger] matrix[i][j] <= 4_000_000i32,
        decreases n - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < n
            invariant
                0 <= c <= n,
                0 <= r < n,
                1 <= n <= 300,
                row.len() == c as int,
                values.len() == n * n,
                forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 4_000_000i32,
                forall|j: int| 0 <= j < c ==> 1 <= #[trigger] row[j] <= 4_000_000i32,
            decreases n - c,
        {
            assert(r * n + c < n * n) by {
                assert(r < n);
                assert(c < n);
                assert(r * n <= (n - 1) * n) by (nonlinear_arith)
                    requires r < n, 1 <= n <= 300;
                assert((n - 1) * n + c < n * n) by (nonlinear_arith)
                    requires c < n, 1 <= n <= 300;
            };
            let idx: usize = r * n + c;
            let val: i32 = if mutation_kind == 1 && (c == r || c == n - 1 - r) {
                2i32
            } else if mutation_kind == 2 {
                1i32
            } else if mutation_kind == 3 && (c == r || c == n - 1 - r) {
                3_999_989i32
            } else if mutation_kind == 4 && c == r {
                4_000_000i32
            } else {
                values[idx]
            };
            row.push(val);
            c += 1;
        }
        matrix.push(row);

        assert(matrix[r as int].len() == n);

        proof {
            assert forall|i: int| 0 <= i < r + 1 implies (#[trigger] matrix[i]).len() == n by {
                if i < r as int {
                } else {
                    assert(i == r as int);
                    assert(matrix[i].len() == n);
                }
            };
            assert forall|i: int, j: int|
                0 <= i < r + 1 && 0 <= j < n implies
                1 <= #[trigger] matrix[i][j] <= 4_000_000i32 by {
                if i < r as int {
                } else {
                    assert(i == r as int);
                }
            };
        }

        r += 1;
    }

    matrix
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self {
            state: seed.wrapping_add(0x9E3779B97F4A7C15),
        }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
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

fn random_flat_values(rng: &mut Rng, count: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut vals = Vec::with_capacity(count);
    for _ in 0..count {
        vals.push(rng.gen_range_i64(lo as i64, hi as i64) as i32);
    }
    vals
}

fn print_json(nums: &[Vec<i32>]) {
    print!("{{\"nums\":[");
    for (i, row) in nums.iter().enumerate() {
        if i > 0 {
            print!(",");
        }
        print!("[");
        for (j, v) in row.iter().enumerate() {
            if j > 0 {
                print!(",");
            }
            print!("{}", v);
        }
        print!("]");
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2614);
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];

    for t in 0..total {
        let n: usize = match t % 7 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => rng.gen_range_usize(4, 12),
            4 => rng.gen_range_usize(13, 40),
            5 => rng.gen_range_usize(41, 80),
            _ => rng.gen_range_usize(81, 120),
        };
        let mk = mutation_kinds[t % mutation_kinds.len()];
        let vals = if t % 3 == 0 {
            random_flat_values(&mut rng, n * n, 1, 10)
        } else {
            random_flat_values(&mut rng, n * n, 1, 4_000_000)
        };
        let grid = generate_test_case(n, &vals, mk);
        print_json(&grid);
    }
}
