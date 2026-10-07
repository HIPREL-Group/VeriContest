use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    x0: i32, y0: i32,
    x1: i32, y1: i32,
    x2: i32, y2: i32,
) -> (points: Vec<Vec<i32>>)
    requires
        0 <= x0 <= 100,
        0 <= y0 <= 100,
        0 <= x1 <= 100,
        0 <= y1 <= 100,
        0 <= x2 <= 100,
        0 <= y2 <= 100,
    ensures
        points.len() == 3,
        points[0].len() == 2,
        points[1].len() == 2,
        points[2].len() == 2,
        0 <= points[0][0] <= 100,
        0 <= points[0][1] <= 100,
        0 <= points[1][0] <= 100,
        0 <= points[1][1] <= 100,
        0 <= points[2][0] <= 100,
        0 <= points[2][1] <= 100,
{
    let mut points: Vec<Vec<i32>> = Vec::new();

    let mut p0: Vec<i32> = Vec::new();
    p0.push(x0);
    p0.push(y0);
    assert(p0.len() == 2);
    assert(0 <= p0[0] <= 100);
    assert(0 <= p0[1] <= 100);
    points.push(p0);

    let mut p1: Vec<i32> = Vec::new();
    p1.push(x1);
    p1.push(y1);
    assert(p1.len() == 2);
    assert(0 <= p1[0] <= 100);
    assert(0 <= p1[1] <= 100);
    points.push(p1);

    let mut p2: Vec<i32> = Vec::new();
    p2.push(x2);
    p2.push(y2);
    assert(p2.len() == 2);
    assert(0 <= p2[0] <= 100);
    assert(0 <= p2[1] <= 100);
    points.push(p2);

    assert(points.len() == 3);
    assert(points[0].len() == 2);
    assert(points[1].len() == 2);
    assert(points[2].len() == 2);

    points
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
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as u32).wrapping_sub(lo as u32).wrapping_add(1);
        let v = (self.next_u64() % span as u64) as i32;
        lo + v
    }

    fn gen_bool(&mut self) -> bool {
        (self.next_u64() & 1) == 0
    }
}

fn cross(points: &Vec<Vec<i32>>) -> i32 {
    let x0 = points[0][0];
    let y0 = points[0][1];
    let x1 = points[1][0];
    let y1 = points[1][1];
    let x2 = points[2][0];
    let y2 = points[2][1];
    (x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)
}

fn random_point(rng: &mut Rng) -> (i32, i32) {
    (rng.gen_range_i32(0, 100), rng.gen_range_i32(0, 100))
}

fn make_case(mode: usize, rng: &mut Rng) -> Vec<Vec<i32>> {
    match mode {
        0 => generate_test_case(0, 0, 1, 1, 2, 2), // diagonal collinear
        1 => generate_test_case(0, 0, 0, 1, 0, 2), // vertical collinear
        2 => generate_test_case(0, 0, 1, 0, 2, 0), // horizontal collinear
        3 => generate_test_case(0, 0, 100, 100, 100, 0), // boundary non-collinear
        4 => generate_test_case(100, 100, 99, 98, 97, 96), // near boundary often collinear-ish
        5 => generate_test_case(42, 42, 42, 42, 43, 44), // duplicate first two
        6 => generate_test_case(7, 8, 9, 10, 7, 8), // duplicate first and third
        7 => generate_test_case(5, 5, 6, 6, 6, 6), // two equal x/y patterns
        8 => {
            let x = rng.gen_range_i32(0, 100);
            let y = rng.gen_range_i32(0, 100);
            let dx = rng.gen_range_i32(0, 50);
            let dy = rng.gen_range_i32(0, 50);
            let x1 = (x + dx).min(100);
            let y1 = (y + dy).min(100);
            let x2 = (x + 2 * dx).min(100);
            let y2 = (y + 2 * dy).min(100);
            generate_test_case(x, y, x1, y1, x2, y2) // constructed collinear / degenerate
        }
        9 => {
            let (x0, y0) = random_point(rng);
            let (x1, y1) = random_point(rng);
            let mut x2 = rng.gen_range_i32(0, 100);
            let mut y2 = rng.gen_range_i32(0, 100);
            if (x1 - x0) * (y2 - y0) == (x2 - x0) * (y1 - y0) {
                y2 = (y2 + 1).min(100);
                if (x1 - x0) * (y2 - y0) == (x2 - x0) * (y1 - y0) {
                    x2 = (x2 + 1).min(100);
                }
            }
            generate_test_case(x0, y0, x1, y1, x2, y2)
        }
        _ => {
            if rng.gen_bool() {
                let x = rng.gen_range_i32(0, 100);
                let y = rng.gen_range_i32(0, 100);
                let mut x1 = rng.gen_range_i32(0, 100);
                let mut y1 = rng.gen_range_i32(0, 100);
                if x1 == x && y1 == y {
                    x1 = (x1 + 1).min(100);
                }
                generate_test_case(x, y, x1, y1, x, y)
            } else {
                let (x0, y0) = random_point(rng);
                let (x1, y1) = random_point(rng);
                let (x2, y2) = random_point(rng);
                generate_test_case(x0, y0, x1, y1, x2, y2)
            }
        }
    }
}

fn print_json_case(points: &Vec<Vec<i32>>) {
    println!(
        "{{\"points\":[[{0},{1}],[{2},{3}],[{4},{5}]]}}",
        points[0][0],
        points[0][1],
        points[1][0],
        points[1][1],
        points[2][0],
        points[2][1]
    );
}

fn main() {
    let seed = std::env::args()
        .nth(1)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(1);

    let mut rng = Rng::new(seed);

    for i in 0..200usize {
        let mode = if i < 120 { i % 10 } else { 10 + (i % 2) };
        let points = make_case(mode, &mut rng);
        let _ = cross(&points);
        print_json_case(&points);
    }
}