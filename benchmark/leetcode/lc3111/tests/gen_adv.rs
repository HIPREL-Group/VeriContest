use vstd::prelude::*;

verus! {

pub fn construct_points(raw: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == 2,
        forall|i: int| 0 <= i < result.len() ==> 0 <= (#[trigger] result[i])[0] <= 1000000000 && 0 <= result[i][1] <= 1000000000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i]@ != result[j]@,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let end = if raw.len() > 100000 { 100000usize } else { raw.len() };
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;
    while i < end
        invariant
            0 <= i <= end <= raw.len(), end <= 100000, result.len() <= i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j].len() == 2,
            forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j][0] <= 1000000000 && 0 <= result[j][1] <= 1000000000,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> (#[trigger] result[j][0] < #[trigger] result[k][0] || (#[trigger] result[j][0] == #[trigger] result[k][0] && #[trigger] result[j][1] < #[trigger] result[k][1])),
        decreases end - i,
    {
        let x = if raw[i].len() > 0 { raw[i][0] } else { 0 };
        let y = if raw[i].len() > 1 { raw[i][1] } else { 0 };
        let x = if x < 0 { 0 } else if x > 1000000000 { 1000000000 } else { x };
        let y = if y < 0 { 0 } else if y > 1000000000 { 1000000000 } else { y };
        let mut accept = true;
        if result.len() > 0 {
            let last = result.len() - 1;
            assert(result[last as int].len() == 2);
            accept = result[last][0] < x || (result[last][0] == x && result[last][1] < y);
        }
        if accept {
            assert forall|j: int| 0 <= j < result.len() implies
                (result[j][0] < x || (result[j][0] == x && result[j][1] < y)) by {
                if j < result.len() - 1 { assert((result[j][0] < result[result.len() - 1][0] || (result[j][0] == result[result.len() - 1][0] && result[j][1] < result[result.len() - 1][1]))); }
            }
            let mut p = Vec::new();
            p.push(x);
            p.push(y);
            result.push(p);
        }
        i += 1;
    }
    if result.len() < 1 {
        let mut fallback: Vec<Vec<i32>> = Vec::new();
        let mut p = Vec::new();
        p.push(0);
        p.push(0);
        fallback.push(p);

        fallback
    } else {
        assert forall|j: int, k: int| 0 <= j < k < result.len()
            implies result[j]@ != result[k]@ by {
            assert((result[j][0] < result[k][0] || (result[j][0] == result[k][0] && result[j][1] < result[k][1])));
        }
        result
    }
}

pub fn generate_test_case(points: Vec<Vec<i32>>, w: i32) -> (result: (Vec<Vec<i32>>, i32))
    ensures
        1 <= result.0.len() <= 100000,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == 2,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= (#[trigger] result.0[i])[0] <= 1000000000 && 0 <= result.0[i][1] <= 1000000000,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i]@ != result.0[j]@,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] != result.0[j],
        0 <= result.1 <= 1000000000,
{
    (construct_points(points), if w < 0 { 0 } else if w > 1000000000 { 1000000000 } else { w })
}


pub fn generate_candidate(
    xs: &Vec<i32>,
    ys: &Vec<i32>,
    w: i32,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        1 <= xs.len() <= 100000,
        xs.len() == ys.len(),
        forall|i: int| 0 <= i < xs.len() ==> 0 <= #[trigger] xs[i] <= 1000000000,
        forall|i: int| 0 <= i < ys.len() ==> 0 <= #[trigger] ys[i] <= 1000000000,
        0 <= w <= 1000000000,
    ensures
        true,
{
    let mut p: Vec<i32> = Vec::new();
    p.push(0);
    p.push(0);
    let mut points: Vec<Vec<i32>> = Vec::new();
    points.push(p);
    (points, w)
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
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
}

fn print_json(points: &Vec<Vec<i32>>, w: i32) {
        let mut points = points.clone();
        points.sort();
        let (points, w) = generate_test_case(points, w);
    print!("{{\"points\":[");
    for i in 0..points.len() {
        if i > 0 {
            print!(",");
        }
        print!("[{},{}]", points[i][0], points[i][1]);
    }
    println!("],\"w\":{}}}", w);
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
    let xs = vec![0];
    let ys = vec![0];
    for _ in 0..total {
        let w = (rng.next_u64() % 1001) as i32;
        let (points, wr) = generate_candidate(&xs, &ys, w);
        print_json(&points, wr);
    }
}
