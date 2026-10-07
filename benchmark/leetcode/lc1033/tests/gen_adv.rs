use vstd::prelude::*;

verus! {

pub open spec fn distinct3(a: int, b: int, c: int) -> bool {
    a != b && b != c && a != c
}

pub fn generate_test_case(lo: i32, mid_gap: i32, hi_gap: i32) -> (result: (i32, i32, i32))
    requires
        1 <= lo <= 98,
        1 <= mid_gap <= 99,
        1 <= hi_gap <= 99,
        lo as int + mid_gap as int <= 99,
        lo as int + mid_gap as int + hi_gap as int <= 100,
    ensures
        ({
            let a = result.0;
            let b = result.1;
            let c = result.2;
            1 <= a <= 100 &&
            1 <= b <= 100 &&
            1 <= c <= 100 &&
            a != b &&
            b != c &&
            a != c
        }),
{
    let a = lo;
    let b = lo + mid_gap;
    let c = b + hi_gap;

    assert(1 <= a);
    assert(a <= 100);

    assert(1 <= b) by {
        assert(1 <= lo);
        assert(1 <= mid_gap);
        assert(lo + mid_gap >= 1);
    }
    assert(b <= 100) by {
        assert(lo as int + mid_gap as int <= 99);
    }

    assert(1 <= c) by {
        assert(1 <= b);
        assert(1 <= hi_gap);
        assert(b + hi_gap >= 1);
    }
    assert(c <= 100) by {
        assert(lo as int + mid_gap as int + hi_gap as int <= 100);
        assert(c as int == lo as int + mid_gap as int + hi_gap as int);
    }

    assert(a != b) by {
        assert(mid_gap > 0);
        assert(b == a + mid_gap);
    }
    assert(b != c) by {
        assert(hi_gap > 0);
        assert(c == b + hi_gap);
    }
    assert(a != c) by {
        assert(mid_gap > 0);
        assert(hi_gap > 0);
        assert(c == a + mid_gap + hi_gap);
    }

    (a, b, c)
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }

    fn gen_bool(&mut self) -> bool {
        (self.next_u64() & 1) == 1
    }
}

fn sort3(mut a: i32, mut b: i32, mut c: i32) -> (i32, i32, i32) {
    if a > b {
        std::mem::swap(&mut a, &mut b);
    }
    if b > c {
        std::mem::swap(&mut b, &mut c);
    }
    if a > b {
        std::mem::swap(&mut a, &mut b);
    }
    (a, b, c)
}

fn make_case_from_sorted(lo: i32, mid: i32, hi: i32, perm: u64) -> (i32, i32, i32) {
    match perm % 6 {
        0 => (lo, mid, hi),
        1 => (lo, hi, mid),
        2 => (mid, lo, hi),
        3 => (mid, hi, lo),
        4 => (hi, lo, mid),
        _ => (hi, mid, lo),
    }
}

fn adversarial_case(mode: usize, rng: &mut Rng) -> (i32, i32, i32) {
    match mode {
        0 => {
            let lo = 1;
            let mid_gap = 1;
            let hi_gap = 1;
            let (a, b, c) = generate_test_case(lo, mid_gap, hi_gap);
            make_case_from_sorted(a, b, c, rng.next_u64())
        }
        1 => {
            let lo = rng.gen_range_i32(1, 98);
            let mid_gap = 1;
            let hi_gap = 2;
            let (a, b, c) = generate_test_case(lo, mid_gap, hi_gap);
            make_case_from_sorted(a, b, c, rng.next_u64())
        }
        2 => {
            let lo = rng.gen_range_i32(1, 97);
            let mid_gap = 2;
            let hi_gap = 1;
            let (a, b, c) = generate_test_case(lo, mid_gap, hi_gap);
            make_case_from_sorted(a, b, c, rng.next_u64())
        }
        3 => {
            let lo = rng.gen_range_i32(1, 96);
            let mid_gap = 2;
            let hi_gap = 2;
            let (a, b, c) = generate_test_case(lo, mid_gap, hi_gap);
            make_case_from_sorted(a, b, c, rng.next_u64())
        }
        4 => {
            let lo = 1;
            let mid_gap = 1;
            let hi_gap = 98;
            let (a, b, c) = generate_test_case(lo, mid_gap, hi_gap);
            make_case_from_sorted(a, b, c, rng.next_u64())
        }
        5 => {
            let lo = 1;
            let mid_gap = 98;
            let hi_gap = 1;
            let (a, b, c) = generate_test_case(lo, mid_gap, hi_gap);
            make_case_from_sorted(a, b, c, rng.next_u64())
        }
        6 => {
            let lo = 1;
            let mid_gap = 49;
            let hi_gap = 50;
            let (a, b, c) = generate_test_case(lo, mid_gap, hi_gap);
            make_case_from_sorted(a, b, c, rng.next_u64())
        }
        7 => {
            let lo = 2;
            let mid_gap = 48;
            let hi_gap = 48;
            let (a, b, c) = generate_test_case(lo, mid_gap, hi_gap);
            make_case_from_sorted(a, b, c, rng.next_u64())
        }
        8 => {
            let lo = 98;
            let mid_gap = 1;
            let hi_gap = 1;
            let (a, b, c) = generate_test_case(lo, mid_gap, hi_gap);
            make_case_from_sorted(a, b, c, rng.next_u64())
        }
        9 => {
            let lo = 97;
            let mid_gap = 1;
            let hi_gap = 2;
            let (a, b, c) = generate_test_case(lo, mid_gap, hi_gap);
            make_case_from_sorted(a, b, c, rng.next_u64())
        }
        _ => {
            let lo = rng.gen_range_i32(1, 98);
            let max_mid_gap = 99 - lo;
            let mid_gap = rng.gen_range_i32(1, max_mid_gap);
            let max_hi_gap = 100 - (lo + mid_gap);
            let hi_gap = rng.gen_range_i32(1, max_hi_gap);
            let (a, b, c) = generate_test_case(lo, mid_gap, hi_gap);
            make_case_from_sorted(a, b, c, rng.next_u64())
        }
    }
}

fn random_case(rng: &mut Rng) -> (i32, i32, i32) {
    let lo = rng.gen_range_i32(1, 98);
    let max_mid_gap = 99 - lo;
    let mut mid_gap = rng.gen_range_i32(1, max_mid_gap);
    let max_hi_gap = 100 - (lo + mid_gap);
    let mut hi_gap = if max_hi_gap >= 1 { rng.gen_range_i32(1, max_hi_gap) } else { 1 };

    if rng.gen_bool() && lo <= 97 {
        mid_gap = 1;
        hi_gap = rng.gen_range_i32(1, 100 - (lo + mid_gap));
    } else if rng.gen_bool() && lo <= 96 {
        mid_gap = 2;
        hi_gap = rng.gen_range_i32(1, 100 - (lo + mid_gap));
    }

    let (a, b, c) = generate_test_case(lo, mid_gap, hi_gap);
    make_case_from_sorted(a, b, c, rng.next_u64())
}

fn main() {
    use std::env;
    use std::io::{self, Write};

    let seed = env::args()
        .nth(1)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(1);

    let mut rng = Rng::new(seed);
    let stdout = io::stdout();
    let mut out = io::BufWriter::new(stdout.lock());

    let total: usize = 200;
    let adv_modes: usize = 10;

    for i in 0..total {
        let (a, b, c) = if i < 120 {
            adversarial_case(i % adv_modes, &mut rng)
        } else {
            random_case(&mut rng)
        };

        let (x, y, z) = sort3(a, b, c);
        assert!(1 <= x && x <= 100);
        assert!(1 <= y && y <= 100);
        assert!(1 <= z && z <= 100);
        assert!(x != y && y != z && x != z);

        writeln!(out, "{{\"a\": {}, \"b\": {}, \"c\": {}}}", a, b, c).unwrap();
    }
}