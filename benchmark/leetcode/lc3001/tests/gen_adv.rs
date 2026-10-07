use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a: i32, b: i32, c: i32, d: i32, e: i32, f: i32,
) -> (result: (i32, i32, i32, i32, i32, i32))
    requires
        1 <= a <= 8,
        1 <= b <= 8,
        1 <= c <= 8,
        1 <= d <= 8,
        1 <= e <= 8,
        1 <= f <= 8,
        a != c || b != d,
        a != e || b != f,
        c != e || d != f,
    ensures
        ({
            let (ra, rb, rc, rd, re, rf) = result;
            &&& 1 <= ra <= 8
            &&& 1 <= rb <= 8
            &&& 1 <= rc <= 8
            &&& 1 <= rd <= 8
            &&& 1 <= re <= 8
            &&& 1 <= rf <= 8
            &&& (ra != rc || rb != rd)
            &&& (ra != re || rb != rf)
            &&& (rc != re || rd != rf)
        }),
{
    (a, b, c, d, e, f)
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
    fn range(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn random_valid(rng: &mut Rng) -> (i32, i32, i32, i32, i32, i32) {
    loop {
        let a = rng.range(1, 8);
        let b = rng.range(1, 8);
        let c = rng.range(1, 8);
        let d = rng.range(1, 8);
        let e = rng.range(1, 8);
        let f = rng.range(1, 8);
        if (a == c && b == d) || (a == e && b == f) || (c == e && d == f) {
            continue;
        }
        return (a, b, c, d, e, f);
    }
}

fn pick_distinct(rng: &mut Rng, ax: i32, ay: i32, bx: i32, by: i32) -> (i32, i32) {
    loop {
        let x = rng.range(1, 8);
        let y = rng.range(1, 8);
        if (x == ax && y == ay) || (x == bx && y == by) { continue; }
        return (x, y);
    }
}

fn mode_rook_row(rng: &mut Rng) -> (i32, i32, i32, i32, i32, i32) {
    // rook and queen share row, bishop elsewhere
    let a = rng.range(1, 8);
    let b = rng.range(1, 8);
    let mut f = rng.range(1, 8);
    while f == b { f = rng.range(1, 8); }
    let e = a;
    let (c, d) = pick_distinct(rng, a, b, e, f);
    (a, b, c, d, e, f)
}

fn mode_rook_col(rng: &mut Rng) -> (i32, i32, i32, i32, i32, i32) {
    let a = rng.range(1, 8);
    let b = rng.range(1, 8);
    let mut e = rng.range(1, 8);
    while e == a { e = rng.range(1, 8); }
    let f = b;
    let (c, d) = pick_distinct(rng, a, b, e, f);
    (a, b, c, d, e, f)
}

fn mode_rook_blocked_row(rng: &mut Rng) -> (i32, i32, i32, i32, i32, i32) {
    // rook and queen share row, bishop between them
    let a = rng.range(1, 8);
    let b = rng.range(1, 3);
    let f = rng.range(b + 3, 8);
    let e = a;
    let c = a;
    let d = rng.range(b + 1, f - 1);
    (a, b, c, d, e, f)
}

fn mode_rook_blocked_col(rng: &mut Rng) -> (i32, i32, i32, i32, i32, i32) {
    let b = rng.range(1, 8);
    let a = rng.range(1, 3);
    let e = rng.range(a + 3, 8);
    let f = b;
    let d = b;
    let c = rng.range(a + 1, e - 1);
    (a, b, c, d, e, f)
}

fn mode_bishop_diag1(rng: &mut Rng) -> (i32, i32, i32, i32, i32, i32) {
    // c+d == e+f
    loop {
        let c = rng.range(1, 8);
        let d = rng.range(1, 8);
        let s = c + d;
        // pick e != c on same anti-diagonal
        let mut candidates = Vec::new();
        for e in 1..=8 {
            let f = s - e;
            if f >= 1 && f <= 8 && e != c {
                candidates.push((e, f));
            }
        }
        if candidates.is_empty() { continue; }
        let (e, f) = candidates[(rng.next_u64() as usize) % candidates.len()];
        let (a, b) = pick_distinct(rng, c, d, e, f);
        return (a, b, c, d, e, f);
    }
}

fn mode_bishop_diag2(rng: &mut Rng) -> (i32, i32, i32, i32, i32, i32) {
    loop {
        let c = rng.range(1, 8);
        let d = rng.range(1, 8);
        let df = c - d;
        let mut candidates = Vec::new();
        for e in 1..=8 {
            let f = e - df;
            if f >= 1 && f <= 8 && e != c {
                candidates.push((e, f));
            }
        }
        if candidates.is_empty() { continue; }
        let (e, f) = candidates[(rng.next_u64() as usize) % candidates.len()];
        let (a, b) = pick_distinct(rng, c, d, e, f);
        return (a, b, c, d, e, f);
    }
}

fn mode_bishop_blocked(rng: &mut Rng) -> (i32, i32, i32, i32, i32, i32) {
    // bishop-queen diag with rook between
    loop {
        let c = rng.range(1, 6);
        let d = rng.range(1, 6);
        let e = c + 2 + ((rng.next_u64() as i32) % (8 - c - 1)).max(0);
        let f = d + (e - c);
        if e < 1 || e > 8 || f < 1 || f > 8 || e == c { continue; }
        // rook between
        let a = c + 1;
        let b = d + 1;
        if a == e && b == f { continue; }
        return (a, b, c, d, e, f);
    }
}

fn mode_corner(rng: &mut Rng) -> (i32, i32, i32, i32, i32, i32) {
    let corners = [(1,1),(1,8),(8,1),(8,8)];
    let p1 = corners[(rng.next_u64() as usize) % 4];
    let p2 = corners[(rng.next_u64() as usize) % 4];
    let p3 = corners[(rng.next_u64() as usize) % 4];
    if p1 == p2 || p1 == p3 || p2 == p3 {
        return random_valid(rng);
    }
    (p1.0, p1.1, p2.0, p2.1, p3.0, p3.1)
}

fn mode_adjacent(rng: &mut Rng) -> (i32, i32, i32, i32, i32, i32) {
    // queen adjacent to rook
    let a = rng.range(2, 7);
    let b = rng.range(2, 7);
    let e = a;
    let f = b + 1;
    let (c, d) = pick_distinct(rng, a, b, e, f);
    (a, b, c, d, e, f)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200;
    for t in 0..total {
        let mode = t % 10;
        let tc = match mode {
            0 => random_valid(&mut rng),
            1 => mode_rook_row(&mut rng),
            2 => mode_rook_col(&mut rng),
            3 => mode_rook_blocked_row(&mut rng),
            4 => mode_rook_blocked_col(&mut rng),
            5 => mode_bishop_diag1(&mut rng),
            6 => mode_bishop_diag2(&mut rng),
            7 => mode_bishop_blocked(&mut rng),
            8 => mode_corner(&mut rng),
            _ => mode_adjacent(&mut rng),
        };
        // validate: if bad, fall back
        let (a, b, c, d, e, f) = tc;
        let valid = a >= 1 && a <= 8 && b >= 1 && b <= 8
            && c >= 1 && c <= 8 && d >= 1 && d <= 8
            && e >= 1 && e <= 8 && f >= 1 && f <= 8
            && !(a == c && b == d)
            && !(a == e && b == f)
            && !(c == e && d == f);
        let (a, b, c, d, e, f) = if valid { tc } else { random_valid(&mut rng) };

        let (a, b, c, d, e, f) = generate_test_case(a, b, c, d, e, f);
        println!("{{\"a\": {}, \"b\": {}, \"c\": {}, \"d\": {}, \"e\": {}, \"f\": {}}}",
            a, b, c, d, e, f);
    }
}