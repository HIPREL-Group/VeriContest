use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    idx_a: usize,
    idx_b: usize,
    color_a: i32,
    color_b: i32,
    fillers: &Vec<i32>,
) -> (colors: Vec<i32>)
    requires
        2 <= n <= 100,
        n == fillers.len() + 2,
        idx_a < n,
        idx_b < n,
        idx_a != idx_b,
        0 <= color_a <= 100,
        0 <= color_b <= 100,
        color_a != color_b,
        forall |i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 100,
    ensures
        2 <= colors.len() <= 100,
        forall |i: int| 0 <= i < colors.len() ==> 0 <= #[trigger] colors[i] <= 100,
        exists |i: int, j: int| 0 <= i < j < colors.len() && colors[i] != colors[j],
{
    let mut colors: Vec<i32> = Vec::new();
    let mut pos: usize = 0;
    let mut fi: usize = 0;

    while pos < n
        invariant
            n == fillers.len() + 2,
            2 <= n <= 100,
            0 <= pos <= n,
            colors.len() == pos,
            idx_a < n,
            idx_b < n,
            idx_a != idx_b,
            0 <= color_a <= 100,
            0 <= color_b <= 100,
            0 <= fi <= fillers.len(),
            fi == pos - (if idx_a < pos { 1usize } else { 0usize })
                      - (if idx_b < pos { 1usize } else { 0usize }),
            forall |k: int| 0 <= k < pos as int ==> 0 <= #[trigger] colors[k] <= 100,
            idx_a < pos ==> colors[idx_a as int] == color_a,
            idx_b < pos ==> colors[idx_b as int] == color_b,
            forall |i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 100,
        decreases n - pos,
    {
        if pos == idx_a {
            colors.push(color_a);
        } else if pos == idx_b {
            colors.push(color_b);
        } else {
            assert(fi < fillers.len());
            colors.push(fillers[fi]);
            fi = fi + 1;
        }
        pos = pos + 1;
    }

    proof {
        let lo = if idx_a < idx_b { idx_a as int } else { idx_b as int };
        let hi = if idx_a < idx_b { idx_b as int } else { idx_a as int };
        assert(0 <= lo < hi < colors.len());
        assert(colors[idx_a as int] == color_a);
        assert(colors[idx_b as int] == color_b);
        assert(colors[lo] != colors[hi]);
    }

    colors
}

} // verus!

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize % (hi - lo + 1))
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_two_distinct_indices(rng: &mut Rng, n: usize) -> (usize, usize) {
    let i = rng.gen_usize(0, n - 1);
    let mut j = rng.gen_usize(0, n - 2);
    if j >= i { j += 1; }
    (i, j)
}

fn pick_two_distinct_colors(rng: &mut Rng) -> (i32, i32) {
    let a = rng.gen_i32(0, 100);
    let mut b = rng.gen_i32(0, 99);
    if b >= a { b += 1; }
    (a, b)
}

fn build_fillers(rng: &mut Rng, count: usize, mode: usize, color_a: i32, color_b: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(count);
    for i in 0..count {
        let c = match mode {
            0 => color_a,
            1 => color_b,
            2 => if i % 2 == 0 { color_a } else { color_b },
            3 => 0,
            4 => 100,
            5 => rng.gen_i32(0, 100),
            6 => (i as i32) % 101,
            7 => color_a,
            8 => color_b,
            _ => rng.gen_i32(0, 100),
        };
        v.push(c);
    }
    v
}

fn print_json(colors: &[i32]) {
    print!("{{\"colors\":[");
    for i in 0..colors.len() {
        if i > 0 { print!(","); }
        print!("{}", colors[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    for t in 0..total {
        let mode = t % 10;
        let n: usize = match mode {
            0 => 2,
            1 => 3,
            2 => 100,
            3 => 99,
            4 => rng.gen_usize(2, 10),
            5 => rng.gen_usize(50, 100),
            6 => rng.gen_usize(2, 100),
            7 => 100,
            8 => rng.gen_usize(4, 20),
            _ => rng.gen_usize(2, 100),
        };

        let (color_a, color_b) = match mode {
            3 => (0i32, 100i32),
            7 => (0i32, 1i32),
            _ => pick_two_distinct_colors(&mut rng),
        };

        let (idx_a, idx_b) = match mode {
            0 => (0usize, 1usize),
            1 => (0usize, n - 1),
            2 => (0usize, n - 1),
            3 => (n / 2, n - 1),
            _ => pick_two_distinct_indices(&mut rng, n),
        };

        let filler_mode = t % 9;
        let fillers = build_fillers(&mut rng, n - 2, filler_mode, color_a, color_b);

        let colors = generate_test_case(n, idx_a, idx_b, color_a, color_b, &fillers);
        print_json(&colors);
    }
}