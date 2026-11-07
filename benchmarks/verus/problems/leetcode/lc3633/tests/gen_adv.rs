use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    m: usize,
    land_start_fill: i32,
    land_duration_fill: i32,
    water_start_fill: i32,
    water_duration_fill: i32,
    i_idx: usize,
    j_idx: usize,
) -> (result: (Vec<i32>, Vec<i32>, Vec<i32>, Vec<i32>, usize, usize))
    requires
        1 <= n <= 100,
        1 <= m <= 100,
        1 <= land_start_fill <= 1000,
        1 <= land_duration_fill <= 1000,
        1 <= water_start_fill <= 1000,
        1 <= water_duration_fill <= 1000,
        i_idx < n,
        j_idx < m,
    ensures
        ({
            let (lst, ld, wst, wd, ii, jj) = result;
            &&& 1 <= lst.len() <= 100
            &&& 1 <= wst.len() <= 100
            &&& lst.len() == ld.len()
            &&& wst.len() == wd.len()
            &&& (forall|k: int| 0 <= k < lst.len() ==> 1 <= #[trigger] lst[k] <= 1000)
            &&& (forall|k: int| 0 <= k < ld.len() ==> 1 <= #[trigger] ld[k] <= 1000)
            &&& (forall|k: int| 0 <= k < wst.len() ==> 1 <= #[trigger] wst[k] <= 1000)
            &&& (forall|k: int| 0 <= k < wd.len() ==> 1 <= #[trigger] wd[k] <= 1000)
            &&& ii < lst.len()
            &&& jj < wst.len()
        }),
{
    let mut lst: Vec<i32> = Vec::new();
    let mut ld: Vec<i32> = Vec::new();
    let mut wst: Vec<i32> = Vec::new();
    let mut wd: Vec<i32> = Vec::new();

    let mut a: usize = 0;
    while a < n
        invariant
            a <= n,
            n <= 100,
            lst.len() == a,
            ld.len() == a,
            1 <= land_start_fill <= 1000,
            1 <= land_duration_fill <= 1000,
            forall|k: int| 0 <= k < a as int ==> #[trigger] lst[k] == land_start_fill,
            forall|k: int| 0 <= k < a as int ==> #[trigger] ld[k] == land_duration_fill,
        decreases n - a,
    {
        lst.push(land_start_fill);
        ld.push(land_duration_fill);
        a = a + 1;
    }

    let mut b: usize = 0;
    while b < m
        invariant
            b <= m,
            m <= 100,
            wst.len() == b,
            wd.len() == b,
            1 <= water_start_fill <= 1000,
            1 <= water_duration_fill <= 1000,
            forall|k: int| 0 <= k < b as int ==> #[trigger] wst[k] == water_start_fill,
            forall|k: int| 0 <= k < b as int ==> #[trigger] wd[k] == water_duration_fill,
        decreases m - b,
    {
        wst.push(water_start_fill);
        wd.push(water_duration_fill);
        b = b + 1;
    }

    (lst, ld, wst, wd, i_idx, j_idx)
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_params(rng: &mut Rng, mode: usize) -> (usize, usize, i32, i32, i32, i32, usize, usize) {
    match mode {
        0 => {
            // minimum sizes
            (1, 1, 1, 1, 1, 1, 0, 0)
        }
        1 => {
            // maximum sizes, all 1000
            (100, 100, 1000, 1000, 1000, 1000, 99, 99)
        }
        2 => {
            // max sizes, all 1
            (100, 100, 1, 1, 1, 1, 0, 0)
        }
        3 => {
            // land ends right as water opens
            let ls = rng.gen_range_i32(1, 500);
            let lday = rng.gen_range_i32(1, 500);
            let ws = ls + lday; // water opens exactly when land finishes
            let ws = if ws > 1000 { 1000 } else { ws };
            let wd = rng.gen_range_i32(1, 1000);
            (5, 5, ls, lday, ws, wd, 2, 2)
        }
        4 => {
            // water much later than land
            (10, 10, 1, 1, 1000, 1000, 5, 5)
        }
        5 => {
            // land much later than water
            (10, 10, 1000, 1000, 1, 1, 3, 7)
        }
        6 => {
            // both open at same time
            let t = rng.gen_range_i32(1, 1000);
            let d1 = rng.gen_range_i32(1, 1000);
            let d2 = rng.gen_range_i32(1, 1000);
            (8, 8, t, d1, t, d2, 0, 0)
        }
        7 => {
            // random small
            let n = rng.gen_range_usize(1, 10);
            let m = rng.gen_range_usize(1, 10);
            let ls = rng.gen_range_i32(1, 1000);
            let ld = rng.gen_range_i32(1, 1000);
            let ws = rng.gen_range_i32(1, 1000);
            let wd = rng.gen_range_i32(1, 1000);
            let i = rng.gen_range_usize(0, n - 1);
            let j = rng.gen_range_usize(0, m - 1);
            (n, m, ls, ld, ws, wd, i, j)
        }
        8 => {
            // asymmetric sizes
            let n = 1usize;
            let m = 100usize;
            let ls = rng.gen_range_i32(1, 1000);
            let ld = rng.gen_range_i32(1, 1000);
            let ws = rng.gen_range_i32(1, 1000);
            let wd = rng.gen_range_i32(1, 1000);
            (n, m, ls, ld, ws, wd, 0, 50)
        }
        9 => {
            // asymmetric other way
            let n = 100usize;
            let m = 1usize;
            let ls = rng.gen_range_i32(1, 1000);
            let ld = rng.gen_range_i32(1, 1000);
            let ws = rng.gen_range_i32(1, 1000);
            let wd = rng.gen_range_i32(1, 1000);
            (n, m, ls, ld, ws, wd, 99, 0)
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let m = rng.gen_range_usize(1, 100);
            let ls = rng.gen_range_i32(1, 1000);
            let ld = rng.gen_range_i32(1, 1000);
            let ws = rng.gen_range_i32(1, 1000);
            let wd = rng.gen_range_i32(1, 1000);
            let i = rng.gen_range_usize(0, n - 1);
            let j = rng.gen_range_usize(0, m - 1);
            (n, m, ls, ld, ws, wd, i, j)
        }
    }
}

fn print_vec(v: &[i32]) {
    print!("[");
    for k in 0..v.len() {
        if k > 0 {
            print!(",");
        }
        print!("{}", v[k]);
    }
    print!("]");
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
    let total = 220usize;

    for t in 0..total {
        let mode = if t < modes { t } else { rng.gen_range_usize(0, modes - 1) };
        let (n, m, ls, ld, ws, wd, i, j) = pick_params(&mut rng, mode);
        let (lst, ldv, wst, wdv, ii, jj) =
            generate_test_case(n, m, ls, ld, ws, wd, i, j);

        print!("{{\"land_start_time\":");
        print_vec(&lst);
        print!(",\"land_duration\":");
        print_vec(&ldv);
        print!(",\"water_start_time\":");
        print_vec(&wst);
        print!(",\"water_duration\":");
        print_vec(&wdv);
        print!(",\"i\":{},\"j\":{}}}", ii, jj);
        println!();
    }
}