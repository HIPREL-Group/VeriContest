use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw_bl: Vec<Vec<i32>>, raw_tr: Vec<Vec<i32>>) -> (result: (Vec<Vec<i32>>, Vec<Vec<i32>>))
    ensures
        2 <= result.0.len() <= 1000,
        result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == 2,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i].len() == 2,
        forall|i: int, j: int| #![trigger result.0[i][j]] #![trigger result.1[i][j]]
            0 <= i < result.0.len() && 0 <= j < 2 ==> 1 <= result.0[i][j] < result.1[i][j] <= 10000000,
{
    let n = if raw_bl.len() < 2 { 2usize } else if raw_bl.len() > 1000 { 1000usize } else { raw_bl.len() };
    let mut bl: Vec<Vec<i32>> = Vec::new();
    let mut tr: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            2 <= n <= 1000, 0 <= i <= n, bl.len() == i, tr.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] bl[k].len() == 2,
            forall|k: int| 0 <= k < i ==> #[trigger] tr[k].len() == 2,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < 2 ==> 1 <= #[trigger] bl[k][j] < tr[k][j] <= 10000000,
        decreases n - i,
    {
        let mut lower: Vec<i32> = Vec::new();
        let mut upper: Vec<i32> = Vec::new();
        let mut j = 0usize;
        while j < 2
            invariant
                0 <= j <= 2, lower.len() == j, upper.len() == j,
                forall|k: int| 0 <= k < j ==> 1 <= #[trigger] lower[k] < upper[k] <= 10000000,
            decreases 2 - j,
        {
            let lo = if i < raw_bl.len() && j < raw_bl[i].len() { raw_bl[i][j] } else { 1 };
            let hi = if i < raw_tr.len() && j < raw_tr[i].len() { raw_tr[i][j] } else { 2 };
            let lo = if lo < 1 { 1 } else if lo > 9999999 { 9999999 } else { lo };
            let hi = if hi <= lo { lo + 1 } else if hi > 10000000 { 10000000 } else { hi };
            lower.push(lo);
            upper.push(hi);
            j += 1;
        }
        bl.push(lower);
        tr.push(upper);
        i += 1;
    }
    (bl, tr)
}


pub fn generate_candidate(
    n: usize,
    xs: &Vec<i32>,
    ys: &Vec<i32>,
    ws: &Vec<i32>,
    hs: &Vec<i32>,
) -> (res: (Vec<Vec<i32>>, Vec<Vec<i32>>))
    requires
        2 <= n <= 1_000,
        xs.len() == n,
        ys.len() == n,
        ws.len() == n,
        hs.len() == n,
        forall|i: int| 0 <= i < n as int ==> 1 <= #[trigger] xs[i] <= 9_999_999,
        forall|i: int| 0 <= i < n as int ==> 1 <= #[trigger] ys[i] <= 9_999_999,
        forall|i: int| 0 <= i < n as int ==> 1 <= #[trigger] ws[i] && xs[i] as int + ws[i] as int <= 10_000_000,
        forall|i: int| 0 <= i < n as int ==> 1 <= #[trigger] hs[i] && ys[i] as int + hs[i] as int <= 10_000_000,
    ensures
        res.0.len() == res.1.len(),
        2 <= res.0.len() <= 1_000,
        forall|i: int| 0 <= i < res.0.len() ==> (#[trigger] res.0[i]).len() == 2,
        forall|i: int| 0 <= i < res.1.len() ==> (#[trigger] res.1[i]).len() == 2,
        forall|i: int| 0 <= i < res.0.len() ==>
            res.0[i][0] < res.1[i][0] && res.0[i][1] < res.1[i][1],
        forall|i: int| 0 <= i < res.0.len() ==>
            0 <= #[trigger] res.0[i][0] <= 10_000_000 &&
            0 <= #[trigger] res.0[i][1] <= 10_000_000 &&
            0 <= #[trigger] res.1[i][0] <= 10_000_000 &&
            0 <= #[trigger] res.1[i][1] <= 10_000_000,
{
    let mut bl: Vec<Vec<i32>> = Vec::new();
    let mut tr: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            2 <= n <= 1_000,
            xs.len() == n,
            ys.len() == n,
            ws.len() == n,
            hs.len() == n,
            bl.len() == i,
            tr.len() == i,
            forall|k: int| 0 <= k < n as int ==> 1 <= #[trigger] xs[k] <= 9_999_999,
            forall|k: int| 0 <= k < n as int ==> 1 <= #[trigger] ys[k] <= 9_999_999,
            forall|k: int| 0 <= k < n as int ==> 1 <= #[trigger] ws[k] && xs[k] as int + ws[k] as int <= 10_000_000,
            forall|k: int| 0 <= k < n as int ==> 1 <= #[trigger] hs[k] && ys[k] as int + hs[k] as int <= 10_000_000,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] bl[k]).len() == 2,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] tr[k]).len() == 2,
            forall|k: int| 0 <= k < i as int ==> bl[k][0] == xs[k] && bl[k][1] == ys[k],
            forall|k: int| 0 <= k < i as int ==> tr[k][0] as int == xs[k] as int + ws[k] as int && tr[k][1] as int == ys[k] as int + hs[k] as int,
        decreases n - i,
    {
        let x = xs[i];
        let y = ys[i];
        let w = ws[i];
        let h = hs[i];
        let mut b: Vec<i32> = Vec::new();
        b.push(x);
        b.push(y);
        let mut t: Vec<i32> = Vec::new();
        t.push(x + w);
        t.push(y + h);
        assert(b[0] == x);
        assert(b[1] == y);
        assert(t[0] == x + w);
        assert(t[1] == y + h);
        bl.push(b);
        tr.push(t);
        i = i + 1;
    }

    assert forall|k: int| 0 <= k < bl.len() implies
        bl[k][0] < tr[k][0] && bl[k][1] < tr[k][1] by {
        assert(bl[k][0] == xs[k]);
        assert(tr[k][0] as int == xs[k] as int + ws[k] as int);
        assert(ws[k] >= 1);
        assert(hs[k] >= 1);
    }

    assert forall|k: int| 0 <= k < bl.len() implies
        0 <= #[trigger] bl[k][0] <= 10_000_000 &&
        0 <= #[trigger] bl[k][1] <= 10_000_000 &&
        0 <= #[trigger] tr[k][0] <= 10_000_000 &&
        0 <= #[trigger] tr[k][1] <= 10_000_000 by {
        assert(bl[k][0] == xs[k]);
        assert(bl[k][1] == ys[k]);
        assert(tr[k][0] as int == xs[k] as int + ws[k] as int);
        assert(tr[k][1] as int == ys[k] as int + hs[k] as int);
    }

    (bl, tr)
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i64
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn build_case(rng: &mut Rng, mode: usize, t: usize) -> (usize, Vec<i32>, Vec<i32>, Vec<i32>, Vec<i32>) {
    let n: usize = match mode {
        0 => 2,
        1 => 1_000,
        2 => rng.gen_usize(2, 10),
        3 => rng.gen_usize(50, 200),
        4 => 500,
        5 => 2,
        6 => rng.gen_usize(2, 1_000),
        7 => 3,
        8 => 1_000,
        9 => rng.gen_usize(2, 100),
        _ => rng.gen_usize(2, 500),
    };

    let mut xs: Vec<i32> = Vec::with_capacity(n);
    let mut ys: Vec<i32> = Vec::with_capacity(n);
    let mut ws: Vec<i32> = Vec::with_capacity(n);
    let mut hs: Vec<i32> = Vec::with_capacity(n);

    for i in 0..n {
        let (x, y, w, h) = match mode {
            0 => {
                // random small
                let x = rng.gen_range(1, 100) as i32;
                let y = rng.gen_range(1, 100) as i32;
                let w = rng.gen_range(1, 100) as i32;
                let h = rng.gen_range(1, 100) as i32;
                let w = w.min(10_000_000 - x).max(1);
                let h = h.min(10_000_000 - y).max(1);
                (x, y, w, h)
            }
            1 => {
                // many identical rects
                (1, 1, 9_999_999, 9_999_999)
            }
            2 => {
                // disjoint rects along diagonal
                let base = (i as i32) * 10 + 1;
                (base, base, 5, 5)
            }
            3 => {
                // overlapping squares
                let x = rng.gen_range(1, 1000) as i32;
                let y = rng.gen_range(1, 1000) as i32;
                let s = rng.gen_range(10, 500) as i32;
                let s = s.min(10_000_000 - x.max(y)).max(1);
                (x, y, s, s)
            }
            4 => {
                // large coordinates
                let x = rng.gen_range(1, 9_000_000) as i32;
                let y = rng.gen_range(1, 9_000_000) as i32;
                let w = rng.gen_range(1, 1_000_000) as i32;
                let h = rng.gen_range(1, 1_000_000) as i32;
                let w = w.min(10_000_000 - x).max(1);
                let h = h.min(10_000_000 - y).max(1);
                (x, y, w, h)
            }
            5 => {
                // minimum size
                let x = rng.gen_range(1, 9_999_999) as i32;
                let y = rng.gen_range(1, 9_999_999) as i32;
                (x, y, 1, 1)
            }
            6 => {
                // strip intersections
                let x = 1 + (i as i32 % 100);
                let y = 1;
                (x, y, 50, 9_999_000)
            }
            7 => {
                // nested rectangles
                let pad = i as i32 + 1;
                (pad, pad, 1000 - 2*pad, 1000 - 2*pad)
            }
            8 => {
                // grid pattern
                let gx = (i % 32) as i32;
                let gy = (i / 32) as i32;
                let x = gx * 100 + 1;
                let y = gy * 100 + 1;
                (x, y, 150, 150)
            }
            9 => {
                // all overlap at single point
                let x = rng.gen_range(1, 500) as i32;
                let y = rng.gen_range(1, 500) as i32;
                let w = rng.gen_range(500, 2000) as i32;
                let h = rng.gen_range(500, 2000) as i32;
                let w = w.min(10_000_000 - x).max(1);
                let h = h.min(10_000_000 - y).max(1);
                (x, y, w, h)
            }
            _ => {
                let x = rng.gen_range(1, 5_000_000) as i32;
                let y = rng.gen_range(1, 5_000_000) as i32;
                let w = rng.gen_range(1, 1_000_000) as i32;
                let h = rng.gen_range(1, 1_000_000) as i32;
                let w = w.min(10_000_000 - x).max(1);
                let h = h.min(10_000_000 - y).max(1);
                (x, y, w, h)
            }
        };

        // Ensure constraints: 1 <= x <= 9_999_999, etc, x+w <= 10_000_000
        let x = x.max(1).min(9_999_999);
        let y = y.max(1).min(9_999_999);
        let w = w.max(1).min(10_000_000 - x);
        let h = h.max(1).min(10_000_000 - y);
        let _ = t;

        xs.push(x);
        ys.push(y);
        ws.push(w);
        hs.push(h);
    }

    (n, xs, ys, ws, hs)
}

fn print_json(bl: &Vec<Vec<i32>>, tr: &Vec<Vec<i32>>) {
        let (bl, tr) = generate_test_case(bl.clone(), tr.clone());
    print!("{{\"bl\":[");
    for i in 0..bl.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", bl[i][0], bl[i][1]);
    }
    print!("],\"tr\":[");
    for i in 0..tr.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", tr[i][0], tr[i][1]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, xs, ys, ws, hs) = build_case(&mut rng, mode, t);
        let (bl, tr) = generate_candidate(n, &xs, &ys, &ws, &hs);
        print_json(&bl, &tr);
    }
}
