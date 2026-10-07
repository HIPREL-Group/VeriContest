use vstd::prelude::*;

verus! {

spec fn valid_booking(b: Vec<i32>, n: i32) -> bool {
    b@.len() == 3
        && 1 <= b[0] <= b[1] <= n
        && 1 <= b[2] <= 10_000
}

pub fn generate_test_case(
    n: i32,
    firsts: &Vec<i32>,
    lasts: &Vec<i32>,
    seats: &Vec<i32>,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        1 <= n <= 20_000,
        firsts.len() == lasts.len(),
        lasts.len() == seats.len(),
        1 <= firsts.len() <= 20_000,
        forall|i: int| 0 <= i < firsts.len() ==> 1 <= #[trigger] firsts[i] <= lasts[i] <= n,
        forall|i: int| 0 <= i < seats.len() ==> 1 <= #[trigger] seats[i] <= 10_000,
    ensures
        result.1 == n,
        1 <= result.1 <= 20_000,
        1 <= result.0.len() <= 20_000,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i]@.len() == 3,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i][0] <= result.0[i][1] <= result.1,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i][2] <= 10_000,
{
    let mut bookings: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < firsts.len()
        invariant
            1 <= n <= 20_000,
            firsts.len() == lasts.len(),
            lasts.len() == seats.len(),
            1 <= firsts.len() <= 20_000,
            0 <= i <= firsts.len(),
            bookings.len() == i,
            forall|k: int| 0 <= k < firsts.len() ==> 1 <= #[trigger] firsts[k] <= lasts[k] <= n,
            forall|k: int| 0 <= k < seats.len() ==> 1 <= #[trigger] seats[k] <= 10_000,
            forall|k: int| 0 <= k < bookings.len() ==> #[trigger] bookings[k]@.len() == 3,
            forall|k: int| 0 <= k < bookings.len() ==> bookings[k][0] == firsts[k] && bookings[k][1] == lasts[k] && bookings[k][2] == seats[k],
            forall|k: int| 0 <= k < bookings.len() ==> 1 <= #[trigger] bookings[k][0] <= bookings[k][1] <= n,
            forall|k: int| 0 <= k < bookings.len() ==> 1 <= #[trigger] bookings[k][2] <= 10_000,
        decreases firsts.len() - i,
    {
        let mut b: Vec<i32> = Vec::new();
        b.push(firsts[i]);
        b.push(lasts[i]);
        b.push(seats[i]);
        assert(b@.len() == 3);
        assert(b[0] == firsts[i as int]);
        assert(b[1] == lasts[i as int]);
        assert(b[2] == seats[i as int]);
        bookings.push(b);
        i = i + 1;
    }
    (bookings, n)
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

fn push_booking(firsts: &mut Vec<i32>, lasts: &mut Vec<i32>, seats: &mut Vec<i32>, f: i32, l: i32, s: i32) {
    firsts.push(f);
    lasts.push(l);
    seats.push(s);
}

fn build_case(mode: usize, t: usize, rng: &mut Rng) -> (i32, Vec<i32>, Vec<i32>, Vec<i32>) {
    let n: i32 = match mode {
        0 => 1,
        1 => 2,
        2 => 5,
        3 => 10,
        4 => 31,
        5 => 97,
        6 => 511,
        7 => 1024,
        8 => 19999,
        _ => 20000,
    };

    let mut firsts = Vec::new();
    let mut lasts = Vec::new();
    let mut seats = Vec::new();

    match mode {
        0 => {
            push_booking(&mut firsts, &mut lasts, &mut seats, 1, 1, 1);
        }
        1 => {
            push_booking(&mut firsts, &mut lasts, &mut seats, 1, 2, 10000);
            push_booking(&mut firsts, &mut lasts, &mut seats, 2, 2, 1);
        }
        2 => {
            let mut i = 1;
            while i <= n {
                push_booking(&mut firsts, &mut lasts, &mut seats, i, i, ((i * 37) % 10000) + 1);
                i += 1;
            }
        }
        3 => {
            let m = 40 + (t % 30);
            for _ in 0..m {
                push_booking(&mut firsts, &mut lasts, &mut seats, 1, n, 10000);
            }
        }
        4 => {
            let m = 120;
            for _ in 0..m {
                let x = rng.gen_range_i32(1, n);
                push_booking(&mut firsts, &mut lasts, &mut seats, x, x, rng.gen_range_i32(1, 10000));
            }
        }
        5 => {
            let m = 180;
            for i in 0..m {
                let f = 1 + (i as i32 % n);
                let l = n - (i as i32 % n);
                let (a, b) = if f <= l { (f, l) } else { (l, f) };
                push_booking(&mut firsts, &mut lasts, &mut seats, a, b, ((i as i32 * 97) % 10000) + 1);
            }
        }
        6 => {
            let m = 300;
            for i in 0..m {
                let len = 1 + ((i * 13) % (n as usize)) as i32;
                let start_max = n - len + 1;
                let f = 1 + (rng.gen_range_i32(0, start_max - 1));
                let l = f + len - 1;
                push_booking(&mut firsts, &mut lasts, &mut seats, f, l, rng.gen_range_i32(1, 10000));
            }
        }
        7 => {
            push_booking(&mut firsts, &mut lasts, &mut seats, 1, n, 1);
            push_booking(&mut firsts, &mut lasts, &mut seats, 1, 1, 10000);
            push_booking(&mut firsts, &mut lasts, &mut seats, n, n, 10000);
            let m = 250;
            for _ in 0..m {
                let a = rng.gen_range_i32(1, n);
                let b = rng.gen_range_i32(1, n);
                let (f, l) = if a <= b { (a, b) } else { (b, a) };
                push_booking(&mut firsts, &mut lasts, &mut seats, f, l, rng.gen_range_i32(1, 10000));
            }
        }
        8 => {
            let m = 500;
            for i in 0..m {
                let f = 1 + ((i * 37) % n as usize) as i32;
                let l = 1 + (((i * 91) + 17) % n as usize) as i32;
                let (a, b) = if f <= l { (f, l) } else { (l, f) };
                let s = if i % 2 == 0 { 1 } else { 10000 };
                push_booking(&mut firsts, &mut lasts, &mut seats, a, b, s);
            }
        }
        _ => {
            let m = 20000;
            for i in 0..m {
                let selector = i % 10;
                let (f, l) = match selector {
                    0 => (1, n),
                    1 => (1, 1),
                    2 => (n, n),
                    3 => {
                        let x = 1 + (i % n as usize) as i32;
                        (x, x)
                    }
                    4 => {
                        let len = 1 + ((i * 17) % n as usize) as i32;
                        let f = 1 + (((i * 29) % (n as usize - len as usize + 1)) as i32);
                        (f, f + len - 1)
                    }
                    _ => {
                        let a = rng.gen_range_i32(1, n);
                        let b = rng.gen_range_i32(1, n);
                        if a <= b { (a, b) } else { (b, a) }
                    }
                };
                let s = match selector {
                    0 | 2 | 4 | 6 | 8 => 10000,
                    _ => 1 + ((i * 53) % 10000) as i32,
                };
                push_booking(&mut firsts, &mut lasts, &mut seats, f, l, s);
            }
        }
    }

    if firsts.is_empty() {
        push_booking(&mut firsts, &mut lasts, &mut seats, 1, 1, 1);
    }

    (n, firsts, lasts, seats)
}

fn print_json(bookings: &[Vec<i32>], n: i32) {
    print!("{{\"bookings\":[");
    for i in 0..bookings.len() {
        if i > 0 {
            print!(",");
        }
        print!("[{},{},{}]", bookings[i][0], bookings[i][1], bookings[i][2]);
    }
    println!("],\"n\":{}}}", n);
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
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, firsts, lasts, seats) = build_case(mode, t, &mut rng);
        let (bookings, out_n) = generate_test_case(n, &firsts, &lasts, &seats);
        print_json(&bookings, out_n);
    }
}