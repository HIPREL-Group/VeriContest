use vstd::prelude::*;

verus! {

// Encode queen positions as unique indices 0..64, chosen distinctly.
// Use a filler array `codes` of distinct values in 0..64, skipping king_code.

pub fn generate_test_case(
    king_r: i32,
    king_c: i32,
    codes: &Vec<u8>,  // each code in 0..64, all distinct, none equals king_r*8+king_c
) -> (res: (Vec<Vec<i32>>, Vec<i32>))
    requires
        0 <= king_r < 8,
        0 <= king_c < 8,
        1 <= codes.len() < 64,
        forall |i: int| 0 <= i < codes.len() ==> (#[trigger] codes[i]) < 64,
        forall |i: int| 0 <= i < codes.len() ==> (#[trigger] codes[i]) as int != king_r as int * 8 + king_c as int,
        forall |i: int, j: int| 0 <= i < j < codes.len() ==> codes[i] != codes[j],
    ensures
        ({
            let queens = res.0;
            let king = res.1;
            &&& 1 <= queens.len() < 64
            &&& forall |i: int| 0 <= i < queens.len() ==> (#[trigger] queens[i]).len() == 2
            &&& forall |i: int| 0 <= i < queens.len() ==>
                    0 <= (#[trigger] queens[i])[0] < 8 && 0 <= queens[i][1] < 8
            &&& forall |i: int, j: int| 0 <= i < j < queens.len() ==>
                    !(#[trigger] queens[i][0] == #[trigger] queens[j][0] && queens[i][1] == queens[j][1])
            &&& king.len() == 2
            &&& 0 <= king[0] < 8
            &&& 0 <= king[1] < 8
            &&& forall |i: int| 0 <= i < queens.len() ==>
                    !(#[trigger] queens[i][0] == king[0] && queens[i][1] == king[1])
        }),
{
    let n = codes.len();
    let mut queens: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            n == codes.len(),
            1 <= n < 64,
            0 <= i <= n,
            queens.len() == i,
            0 <= king_r < 8,
            0 <= king_c < 8,
            forall |k: int| 0 <= k < codes.len() ==> (#[trigger] codes[k]) < 64,
            forall |k: int| 0 <= k < codes.len() ==> (#[trigger] codes[k]) as int != king_r as int * 8 + king_c as int,
            forall |a: int, b: int| 0 <= a < b < codes.len() ==> codes[a] != codes[b],
            forall |k: int| 0 <= k < i as int ==> (#[trigger] queens[k]).len() == 2,
            forall |k: int| 0 <= k < i as int ==>
                0 <= (#[trigger] queens[k])[0] < 8 && 0 <= queens[k][1] < 8,
            forall |k: int| 0 <= k < i as int ==>
                #[trigger] queens[k][0] * 8 + queens[k][1] == codes[k] as int,
        decreases n - i,
    {
        let code = codes[i];
        let r = (code / 8) as i32;
        let c = (code % 8) as i32;
        assert(r * 8 + c == code as int) by (nonlinear_arith)
            requires r == (code / 8) as i32, c == (code % 8) as i32, code < 64;
        let mut q: Vec<i32> = Vec::new();
        q.push(r);
        q.push(c);
        assert(q.len() == 2);
        assert(q[0] == r);
        assert(q[1] == c);
        queens.push(q);
        i = i + 1;
    }

    let mut king: Vec<i32> = Vec::new();
    king.push(king_r);
    king.push(king_c);

    assert forall |a: int, b: int| 0 <= a < b < queens.len() implies
        !(#[trigger] queens[a][0] == #[trigger] queens[b][0] && queens[a][1] == queens[b][1])
    by {
        assert(queens[a][0] * 8 + queens[a][1] == codes[a] as int);
        assert(queens[b][0] * 8 + queens[b][1] == codes[b] as int);
        assert(codes[a] != codes[b]);
    }

    assert forall |a: int| 0 <= a < queens.len() implies
        !(#[trigger] queens[a][0] == king[0] && queens[a][1] == king[1])
    by {
        assert(queens[a][0] * 8 + queens[a][1] == codes[a] as int);
        assert(codes[a] as int != king_r as int * 8 + king_c as int);
        assert(king[0] == king_r);
        assert(king[1] == king_c);
    }

    (queens, king)
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
    fn gen_range(&mut self, lo: u64, hi: u64) -> u64 {
        let span = hi - lo + 1;
        lo + self.next_u64() % span
    }
}

fn shuffle(rng: &mut Rng, v: &mut Vec<u8>) {
    let n = v.len();
    if n <= 1 { return; }
    for i in (1..n).rev() {
        let j = (rng.next_u64() as usize) % (i + 1);
        v.swap(i, j);
    }
}

fn make_codes(rng: &mut Rng, king_code: u8, count: usize, picks: &[u8]) -> Vec<u8> {
    // Build a pool of distinct codes in 0..64 excluding king_code, starting with picks (deduped),
    // then fill with shuffled remaining.
    let mut used = [false; 64];
    used[king_code as usize] = true;
    let mut res: Vec<u8> = Vec::new();
    for &p in picks {
        if p < 64 && !used[p as usize] && res.len() < count {
            used[p as usize] = true;
            res.push(p);
        }
    }
    let mut remaining: Vec<u8> = Vec::new();
    for v in 0u8..64 {
        if !used[v as usize] {
            remaining.push(v);
        }
    }
    shuffle(rng, &mut remaining);
    let mut idx = 0;
    while res.len() < count {
        res.push(remaining[idx]);
        idx += 1;
    }
    res
}

fn code_of(r: i32, c: i32) -> u8 { (r * 8 + c) as u8 }

fn adversarial_picks(rng: &mut Rng, mode: usize, kr: i32, kc: i32) -> Vec<u8> {
    let mut picks: Vec<u8> = Vec::new();
    match mode {
        0 => {
            // queens along row of king
            for c in 0..8 { if c != kc { picks.push(code_of(kr, c)); } }
        }
        1 => {
            // queens along column of king
            for r in 0..8 { if r != kr { picks.push(code_of(r, kc)); } }
        }
        2 => {
            // diagonal
            for d in -7..=7 {
                let r = kr + d; let c = kc + d;
                if r >= 0 && r < 8 && c >= 0 && c < 8 && d != 0 {
                    picks.push(code_of(r, c));
                }
            }
        }
        3 => {
            // anti-diagonal
            for d in -7..=7 {
                let r = kr + d; let c = kc - d;
                if r >= 0 && r < 8 && c >= 0 && c < 8 && d != 0 {
                    picks.push(code_of(r, c));
                }
            }
        }
        4 => {
            // all 8 directions, two queens each direction (blocker scenario)
            let dirs: [(i32, i32); 8] = [(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)];
            for &(dr, dc) in &dirs {
                for step in 1..=7 {
                    let r = kr + dr * step; let c = kc + dc * step;
                    if r >= 0 && r < 8 && c >= 0 && c < 8 {
                        picks.push(code_of(r, c));
                    }
                }
            }
        }
        5 => {
            // corners
            picks.push(0);
            picks.push(7);
            picks.push(56);
            picks.push(63);
        }
        6 => {
            // adjacent to king
            for dr in -1i32..=1 {
                for dc in -1i32..=1 {
                    if dr == 0 && dc == 0 { continue; }
                    let r = kr + dr; let c = kc + dc;
                    if r >= 0 && r < 8 && c >= 0 && c < 8 {
                        picks.push(code_of(r, c));
                    }
                }
            }
        }
        7 => {
            // random single queen
            let r = rng.gen_range(0, 7) as i32;
            let c = rng.gen_range(0, 7) as i32;
            if !(r == kr && c == kc) {
                picks.push(code_of(r, c));
            }
        }
        8 => {
            // fill entire board except king
            for v in 0u8..64 {
                if v as i32 != kr * 8 + kc { picks.push(v); }
            }
        }
        _ => {}
    }
    picks
}

fn print_json(queens: &Vec<Vec<i32>>, king: &Vec<i32>) {
    print!("{{\"queens\":[");
    for i in 0..queens.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", queens[i][0], queens[i][1]);
    }
    print!("],\"king\":[{},{}]}}", king[0], king[1]);
    println!();
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
        let kr = (rng.gen_range(0, 7)) as i32;
        let kc = (rng.gen_range(0, 7)) as i32;
        let king_code = code_of(kr, kc);

        // Decide number of queens based on mode.
        let max_n = 63usize;
        let n: usize = match mode {
            0 | 1 => 7,
            2 | 3 => {
                // size of diagonal
                let mut cnt = 0;
                for d in -7i32..=7 {
                    let r = kr + d; let c = if mode == 2 { kc + d } else { kc - d };
                    if r >= 0 && r < 8 && c >= 0 && c < 8 && d != 0 { cnt += 1; }
                }
                std::cmp::max(cnt as usize, 1)
            }
            4 => {
                // up to ~many
                let v = (rng.gen_range(8, 40)) as usize;
                std::cmp::min(v, max_n)
            }
            5 => 4,
            6 => {
                let mut cnt = 0;
                for dr in -1i32..=1 {
                    for dc in -1i32..=1 {
                        if dr == 0 && dc == 0 { continue; }
                        let r = kr + dr; let c = kc + dc;
                        if r >= 0 && r < 8 && c >= 0 && c < 8 { cnt += 1; }
                    }
                }
                std::cmp::max(cnt as usize, 1)
            }
            7 => 1,
            8 => 63,
            _ => {
                let v = (rng.gen_range(1, 30)) as usize;
                std::cmp::min(v, max_n)
            }
        };

        let picks = adversarial_picks(&mut rng, mode, kr, kc);
        let codes = make_codes(&mut rng, king_code, n, &picks);

        let (queens, king) = generate_test_case(kr, kc, &codes);
        print_json(&queens, &king);
    }
}