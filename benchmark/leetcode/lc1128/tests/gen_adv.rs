use vstd::prelude::*;

verus! {

pub open spec fn mk_domino(a: i32, b: i32) -> Seq<i32> {
    seq![a, b]
}

pub fn generate_test_case(
    n: usize,
    special_a: i32,
    special_b: i32,
    special_pos: usize,
    filler_a: i32,
    filler_b: i32,
) -> (dominoes: Vec<Vec<i32>>)
    requires
        1 <= n <= 40_000,
        special_pos < n,
        1 <= special_a <= 9,
        1 <= special_b <= 9,
        1 <= filler_a <= 9,
        1 <= filler_b <= 9,
    ensures
        dominoes.len() == n,
        forall|i: int|
            0 <= i < dominoes.len() ==> (#[trigger] dominoes[i]).len() == 2,
        forall|i: int|
            0 <= i < dominoes.len() ==> 1 <= (#[trigger] dominoes[i])[0] <= 9,
        forall|i: int|
            0 <= i < dominoes.len() ==> 1 <= (#[trigger] dominoes[i])[1] <= 9,
{
    let mut dominoes: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            1 <= n <= 40_000,
            special_pos < n,
            1 <= special_a <= 9,
            1 <= special_b <= 9,
            1 <= filler_a <= 9,
            1 <= filler_b <= 9,
            0 <= i <= n,
            dominoes.len() == i,
            forall|k: int|
                0 <= k < dominoes.len() ==> (#[trigger] dominoes[k]).len() == 2,
            forall|k: int|
                0 <= k < dominoes.len() ==> 1 <= (#[trigger] dominoes[k])[0] <= 9,
            forall|k: int|
                0 <= k < dominoes.len() ==> 1 <= (#[trigger] dominoes[k])[1] <= 9,
        decreases n - i,
    {
        let mut d: Vec<i32> = Vec::new();
        if i == special_pos {
            d.push(special_a);
            d.push(special_b);
        } else {
            d.push(filler_a);
            d.push(filler_b);
        }
        assert(d.len() == 2);
        assert(1 <= d[0] <= 9);
        assert(1 <= d[1] <= 9);
        dominoes.push(d);
        i = i + 1;
    }

    dominoes
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
        self.state = self
            .state
            .wrapping_mul(6364136223846793005u64)
            .wrapping_add(1442695040888963407u64);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn mode_params(rng: &mut Rng, mode: usize, t: usize) -> (usize, i32, i32, usize, i32, i32) {
    match mode {
        0 => {
            let n = 1;
            let a = 1;
            let b = 1;
            let pos = 0;
            let fa = 9;
            let fb = 9;
            (n, a, b, pos, fa, fb)
        }
        1 => {
            let n = 40_000;
            let a = 1;
            let b = 2;
            let pos = 0;
            let fa = 1;
            let fb = 2;
            (n, a, b, pos, fa, fb)
        }
        2 => {
            let n = 40_000;
            let a = 9;
            let b = 9;
            let pos = n - 1;
            let fa = 1;
            let fb = 1;
            (n, a, b, pos, fa, fb)
        }
        3 => {
            let n = 257;
            let a = 2;
            let b = 7;
            let pos = n / 2;
            let fa = 7;
            let fb = 2;
            (n, a, b, pos, fa, fb)
        }
        4 => {
            let n = 199;
            let a = 3;
            let b = 3;
            let pos = 17;
            let fa = 3;
            let fb = 3;
            (n, a, b, pos, fa, fb)
        }
        5 => {
            let n = 211;
            let a = 1;
            let b = 9;
            let pos = 210;
            let fa = 9;
            let fb = 1;
            (n, a, b, pos, fa, fb)
        }
        6 => {
            let n = 37;
            let a = 4;
            let b = 5;
            let pos = 0;
            let fa = 5;
            let fb = 4;
            (n, a, b, pos, fa, fb)
        }
        7 => {
            let n = 1234;
            let a = 8;
            let b = 8;
            let pos = 617;
            let fa = 8;
            let fb = 1;
            (n, a, b, pos, fa, fb)
        }
        8 => {
            let n = 999;
            let a = 1;
            let b = 2;
            let pos = 998;
            let fa = 2;
            let fb = 1;
            (n, a, b, pos, fa, fb)
        }
        9 => {
            let n = 2 + (t % 25);
            let a = ((t % 9) + 1) as i32;
            let b = (((t * 3) % 9) + 1) as i32;
            let pos = t % n;
            let fa = (((t * 5) % 9) + 1) as i32;
            let fb = (((t * 7) % 9) + 1) as i32;
            (n, a, b, pos, fa, fb)
        }
        _ => {
            let n = rng.gen_range_usize(1, 40_000);
            let a = rng.gen_range_i32(1, 9);
            let b = rng.gen_range_i32(1, 9);
            let pos = rng.gen_range_usize(0, n - 1);
            let fa = rng.gen_range_i32(1, 9);
            let fb = rng.gen_range_i32(1, 9);
            (n, a, b, pos, fa, fb)
        }
    }
}

fn print_json_dominoes(dominoes: &[Vec<i32>]) {
    print!("{{\"dominoes\":[");
    for i in 0..dominoes.len() {
        if i > 0 {
            print!(",");
        }
        print!("[{},{}]", dominoes[i][0], dominoes[i][1]);
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
    let total = 200usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, a, b, pos, fa, fb) = mode_params(&mut rng, mode, t);
        let dominoes = generate_test_case(n, a, b, pos, fa, fb);
        print_json_dominoes(&dominoes);
    }
}