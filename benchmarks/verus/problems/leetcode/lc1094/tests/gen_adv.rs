use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn trip_load_at(trip: Vec<i32>, stop: int) -> int
        recommends
            trip@.len() == 3,
    {
        if trip@[1] as int <= stop && stop < trip@[2] as int {
            trip@[0] as int
        } else {
            0
        }
    }

    pub open spec fn load_prefix(trips: Seq<Vec<i32>>, n: int, stop: int) -> int
        recommends
            0 <= n <= trips.len(),
            0 <= stop <= 1000,
            forall |i: int| 0 <= i < trips.len() ==> #[trigger] trips[i]@.len() == 3,
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::load_prefix(trips, n - 1, stop) + Self::trip_load_at(trips[n - 1], stop)
        }
    }
}

pub fn generate_test_case(
    capacity: i32,
    special_passengers: i32,
    special_from: i32,
    special_to: i32,
    fillers: &Vec<(i32, i32, i32)>,
) -> (out: (Vec<Vec<i32>>, i32))
    requires
        1 <= capacity <= 100_000,
        1 <= special_passengers <= 100,
        0 <= special_from < special_to <= 1000,
        fillers.len() <= 999,
        forall|i: int| 0 <= i < fillers.len() ==> {
            let t = #[trigger] fillers[i];
            1 <= t.0 <= 100 && 0 <= t.1 < t.2 <= 1000
        },
    ensures
        1 <= out.0.len() <= 1000,
        out.1 == capacity,
        1 <= out.1 <= 100_000,
        forall|i: int| 0 <= i < out.0.len() ==> #[trigger] out.0[i]@.len() == 3,
        forall|i: int| 0 <= i < out.0.len() ==> 1 <= #[trigger] out.0[i][0] <= 100,
        forall|i: int| 0 <= i < out.0.len() ==> 0 <= #[trigger] out.0[i][1] < out.0[i][2] <= 1000,
{
    let mut trips: Vec<Vec<i32>> = Vec::new();

    let mut first: Vec<i32> = Vec::new();
    first.push(special_passengers);
    first.push(special_from);
    first.push(special_to);
    trips.push(first);

    let mut i: usize = 0;
    while i < fillers.len()
        invariant
            0 <= i <= fillers.len(),
            fillers.len() <= 999,
            trips.len() == i + 1,
            1 <= trips.len() <= 1000,
            1 <= capacity <= 100_000,
            1 <= special_passengers <= 100,
            0 <= special_from < special_to <= 1000,
            trips[0]@.len() == 3,
            trips[0][0] == special_passengers,
            trips[0][1] == special_from,
            trips[0][2] == special_to,
            forall|j: int| 0 <= j < fillers.len() ==> {
                let t = #[trigger] fillers[j];
                1 <= t.0 <= 100 && 0 <= t.1 < t.2 <= 1000
            },
            forall|j: int| 0 <= j < trips.len() ==> #[trigger] trips[j]@.len() == 3,
            forall|j: int| 0 <= j < trips.len() ==> 1 <= #[trigger] trips[j][0] <= 100,
            forall|j: int| 0 <= j < trips.len() ==> 0 <= #[trigger] trips[j][1] < trips[j][2] <= 1000,
            forall|j: int| 1 <= j < trips.len() ==> {
                let t = fillers[j - 1];
                #[trigger] trips[j][0] == t.0 && trips[j][1] == t.1 && trips[j][2] == t.2
            },
        decreases fillers.len() - i,
    {
        let f = fillers[i];
        let mut trip: Vec<i32> = Vec::new();
        trip.push(f.0);
        trip.push(f.1);
        trip.push(f.2);
        trips.push(trip);
        i = i + 1;
    }

    proof {
        assert(trips.len() == fillers.len() + 1);
        assert(1 <= trips.len());
        assert(trips.len() <= 1000);
        assert forall|j: int| 0 <= j < trips.len() implies #[trigger] trips@[j]@.len() == 3 by {
            if j == 0 {
                assert(trips@[0]@.len() == 3);
            } else {
                let t = fillers@[j - 1];
                assert(trips@[j]@[0] == t.0);
                assert(trips@[j]@[1] == t.1);
                assert(trips@[j]@[2] == t.2);
                assert(trips@[j]@.len() == 3);
            }
        };
        assert forall|j: int| 0 <= j < trips.len() implies 1 <= #[trigger] trips@[j]@[0] <= 100 by {
            if j == 0 {
                assert(1 <= trips@[0]@[0] <= 100);
            } else {
                let t = fillers@[j - 1];
                assert(trips@[j]@[0] == t.0);
                assert(1 <= t.0 <= 100);
            }
        };
        assert forall|j: int| 0 <= j < trips.len() implies 0 <= #[trigger] trips@[j]@[1] < trips@[j]@[2] <= 1000 by {
            if j == 0 {
                assert(0 <= trips@[0]@[1] < trips@[0]@[2] <= 1000);
            } else {
                let t = fillers@[j - 1];
                assert(1 <= j && j < trips.len());
                assert(trips[j as int][0] == t.0 && trips[j as int][1] == t.1 && trips[j as int][2] == t.2);
                assert(trips@[j]@[0] == t.0);
                assert(trips@[j]@[1] == t.1);
                assert(trips@[j]@[2] == t.2);
                assert(0 <= t.1 < t.2 <= 1000);
            }
        };
    }

    (trips, capacity)
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

fn make_fillers(count: usize, mode: usize, rng: &mut Rng) -> Vec<(i32, i32, i32)> {
    let mut v = Vec::with_capacity(count);
    let mut i = 0usize;
    while i < count {
        let trip = match mode {
            0 => (1, 0, 1),
            1 => (100, 999, 1000),
            2 => {
                let from = (i % 1000) as i32;
                let to = if from == 999 { 1000 } else { from + 1 };
                (100, from, to)
            }
            3 => {
                let from = (i % 10) as i32;
                (50, from, 1000)
            }
            4 => {
                let to = 1000 - (i % 10) as i32;
                (50, 0, to)
            }
            5 => {
                let from = rng.gen_range_i32(0, 999);
                let to = rng.gen_range_i32(from + 1, 1000);
                (rng.gen_range_i32(1, 100), from, to)
            }
            6 => {
                let base = (i % 500) as i32;
                (1 + (i % 100) as i32, base, base + 1)
            }
            7 => {
                let from = ((i * 37) % 1000) as i32;
                let max_to = if from + 50 <= 1000 { from + 50 } else { 1000 };
                let to = if from + 1 <= max_to {
                    rng.gen_range_i32(from + 1, max_to)
                } else {
                    from + 1
                };
                (100 - (i % 100) as i32, from, to)
            }
            8 => {
                let from = rng.gen_range_i32(0, 998);
                (rng.gen_range_i32(1, 100), from, from + 2)
            }
            _ => {
                let from = ((i * 97 + mode * 13) % 1000) as i32;
                let to = if from == 999 { 1000 } else { from + 1 + ((i % (1000 - from as usize)) as i32) };
                let to2 = if to > 1000 { 1000 } else { to };
                let final_to = if to2 <= from { from + 1 } else { to2 };
                (1 + ((i * 17 + mode) % 100) as i32, from, final_to)
            }
        };
        v.push(trip);
        i += 1;
    }
    v
}

fn print_json(trips: &[Vec<i32>], capacity: i32) {
    print!("{{\"trips\":[");
    for i in 0..trips.len() {
        if i > 0 {
            print!(",");
        }
        print!("[{},{},{}]", trips[i][0], trips[i][1], trips[i][2]);
    }
    println!("],\"capacity\":{}}}", capacity);
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

        let capacity = match mode {
            0 => 1,
            1 => 100_000,
            2 => 4,
            3 => 5,
            4 => 50,
            5 => 100,
            6 => 99999,
            7 => rng.gen_range_i32(1, 100_000),
            8 => 3,
            _ => rng.gen_range_i32(1, 100_000),
        };

        let special = match mode {
            0 => (1, 0, 1),
            1 => (100, 0, 1000),
            2 => (2, 1, 5),
            3 => (3, 3, 7),
            4 => (100, 500, 501),
            5 => (1, 999, 1000),
            6 => (100, 0, 2),
            7 => {
                let from = rng.gen_range_i32(0, 999);
                let to = rng.gen_range_i32(from + 1, 1000);
                (rng.gen_range_i32(1, 100), from, to)
            }
            8 => (2, 1, 5),
            _ => {
                let from = rng.gen_range_i32(0, 999);
                let to = rng.gen_range_i32(from + 1, 1000);
                (rng.gen_range_i32(1, 100), from, to)
            }
        };

        let filler_count = match mode {
            0 => 0,
            1 => 999,
            2 => 1,
            3 => 1,
            4 => 200,
            5 => 50,
            6 => 999,
            7 => rng.gen_range_usize(0, 999),
            8 => 999,
            _ => rng.gen_range_usize(0, 999),
        };

        let fillers = make_fillers(filler_count, mode, &mut rng);
        let (trips, cap) =
            generate_test_case(capacity, special.0, special.1, special.2, &fillers);
        print_json(&trips, cap);
    }
}