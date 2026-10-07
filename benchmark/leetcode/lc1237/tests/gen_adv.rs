use vstd::prelude::*;

verus! {

pub open spec fn row_ok(row: Vec<i32>, x: int) -> bool {
    &&& row@.len() >= 1001
    &&& forall |y: int| 0 <= y <= 1000 ==> #[trigger] row@[y] == (x + y) as i32
}

pub open spec fn grid_ok(values: Seq<Vec<i32>>) -> bool {
    &&& values.len() >= 1001
    &&& forall |x: int| 0 <= x <= 1000 ==> row_ok(#[trigger] values[x], x)
}

pub fn make_row(x: i32) -> (row: Vec<i32>)
    requires 0 <= x <= 1000,
    ensures row_ok(row, x as int),
{
    let mut row: Vec<i32> = Vec::new();
    let mut y: i32 = 0;
    while y <= 1000
        invariant
            0 <= x <= 1000,
            0 <= y <= 1001,
            row@.len() == y as int,
            forall |k: int| 0 <= k < y as int ==> #[trigger] row@[k] == (x + k) as i32,
        decreases 1001i32 - y,
    {
        row.push(x + y);
        y = y + 1;
    }
    row
}

pub fn generate_test_case(z: i32) -> (result: (Vec<Vec<i32>>, i32))
    requires 1 <= z <= 100,
    ensures
        ({
            let values = result.0@;
            let out_z = result.1;
            &&& 1 <= out_z <= 100
            &&& out_z == z
            &&& values.len() >= 1001
            &&& forall |x: int| 0 <= x <= 1000 ==> (#[trigger] values[x])@.len() >= 1001
            &&& forall |x: int, y: int| 1 <= x < 1000 && 1 <= y <= 1000 ==>
                (#[trigger] values[x]@[y]) < values[x + 1]@[y]
            &&& forall |x: int, y: int| 1 <= x <= 1000 && 1 <= y < 1000 ==>
                (#[trigger] values[x]@[y]) < values[x]@[y + 1]
        }),
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut x: i32 = 0;
    while x <= 1000
        invariant
            0 <= x <= 1001,
            grid@.len() == x as int,
            forall |i: int| 0 <= i < x as int ==> row_ok(#[trigger] grid@[i], i),
        decreases 1001i32 - x,
    {
        let row = make_row(x);
        grid.push(row);
        x = x + 1;
    }

    proof {
        assert(grid@.len() == 1001);
        assert forall |xa: int, ya: int| 1 <= xa < 1000 && 1 <= ya <= 1000 implies
            (#[trigger] grid@[xa]@[ya]) < grid@[xa + 1]@[ya]
        by {
            assert(row_ok(grid@[xa], xa));
            assert(row_ok(grid@[xa + 1], xa + 1));
            assert(grid@[xa]@[ya] == (xa + ya) as i32);
            assert(grid@[xa + 1]@[ya] == (xa + 1 + ya) as i32);
        }
        assert forall |xa: int, ya: int| 1 <= xa <= 1000 && 1 <= ya < 1000 implies
            (#[trigger] grid@[xa]@[ya]) < grid@[xa]@[ya + 1]
        by {
            assert(row_ok(grid@[xa], xa));
            assert(grid@[xa]@[ya] == (xa + ya) as i32);
            assert(grid@[xa]@[ya + 1] == (xa + ya + 1) as i32);
        }
    }

    (grid, z)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);

    // adversarial boundary values plus random
    let adversarial: [i32; 10] = [1, 2, 3, 4, 5, 50, 98, 99, 100, 10];

    let total = 200usize;
    for t in 0..total {
        let z: i32 = if t < adversarial.len() {
            adversarial[t]
        } else if t % 7 == 0 {
            1
        } else if t % 7 == 1 {
            100
        } else {
            rng.gen_range_i32(1, 100)
        };
        // We don't actually need to emit the giant grid; just emit z and a small descriptor.
        // But the spec's test input is (customfunction, z). We'll emit just {"z": z} as the
        // test harness is expected to reconstruct f(x,y) = x+y.
        // Actually the required output format in instructions: one JSON per line with fields.
        // Use a simple representation.
        let _ = generate_test_case(z);
        println!("{{\"z\": {}}}", z);
    }
}