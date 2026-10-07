use vstd::prelude::*;

verus! {

pub struct Gen;

impl Gen {
    pub fn generate_test_case(
        shelf_width: i32,
        special_thickness: i32,
        special_height: i32,
        fillers: Vec<i32>,
    ) -> (out: (Vec<Vec<i32>>, i32))
        requires
            1 <= shelf_width <= 1000,
            1 <= special_thickness <= shelf_width,
            1 <= special_height <= 1000,
            0 <= fillers.len() <= 999,
            forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1000,
        ensures
            1 <= out.0.len() <= 1000,
            out.1 == shelf_width,
            1 <= out.1 <= 1000,
            forall |i: int| 0 <= i < out.0.len() ==> #[trigger] out.0[i].len() == 2,
            forall |i: int| 0 <= i < out.0.len() ==> 1 <= #[trigger] out.0[i][0] <= out.1,
            forall |i: int| 0 <= i < out.0.len() ==> 1 <= #[trigger] out.0[i][1] <= 1000,
    {
        let mut books: Vec<Vec<i32>> = Vec::new();

        let mut first: Vec<i32> = Vec::new();
        first.push(special_thickness);
        first.push(special_height);
        books.push(first);

        let mut i: usize = 0;
        while i < fillers.len()
            invariant
                0 <= i <= fillers.len(),
                books.len() == i + 1,
                1 <= shelf_width <= 1000,
                1 <= special_thickness <= shelf_width,
                1 <= special_height <= 1000,
                0 <= fillers.len() <= 999,
                forall |k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 1000,
                books[0].len() == 2,
                books[0][0] == special_thickness,
                books[0][1] == special_height,
                forall |k: int| 1 <= k < books.len() ==> #[trigger] books[k].len() == 2,
                forall |k: int| 1 <= k < books.len() ==> books[k][0] == 1,
                forall |k: int| 1 <= k < books.len() ==> books[k][1] == fillers[k - 1],
            decreases fillers.len() - i,
        {
            let mut b: Vec<i32> = Vec::new();
            b.push(1);
            b.push(fillers[i]);
            books.push(b);
            i = i + 1;
        }

        proof {
            assert(books.len() == fillers.len() + 1);
            assert(1 <= books.len());
            assert(books.len() <= 1000);

            assert forall |k: int| 0 <= k < books.len() implies #[trigger] books[k].len() == 2 by {
                if k == 0 {
                    assert(books[0].len() == 2);
                } else {
                    assert(1 <= k < books.len());
                    assert(books[k].len() == 2);
                }
            };

            assert forall |k: int| 0 <= k < books.len() implies 1 <= #[trigger] books[k][0] <= shelf_width by {
                if k == 0 {
                    assert(books[0][0] == special_thickness);
                    assert(1 <= special_thickness <= shelf_width);
                } else {
                    assert(1 <= k < books.len());
                    assert(books[k][0] == 1);
                    assert(1 <= 1 <= shelf_width);
                }
            };

            assert forall |k: int| 0 <= k < books.len() implies 1 <= #[trigger] books[k][1] <= 1000 by {
                if k == 0 {
                    assert(books[0][1] == special_height);
                    assert(1 <= special_height <= 1000);
                } else {
                    assert(1 <= k < books.len());
                    assert(books[k][1] == fillers[k - 1]);
                    assert(0 <= k - 1 < fillers.len());
                    assert(1 <= fillers[k - 1] <= 1000);
                }
            };
        }

        (books, shelf_width)
    }
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

fn make_fillers(n: usize, mode: usize, shelf_width: i32, rng: &mut Rng) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        let h = match mode {
            0 => 1,
            1 => 1000,
            2 => ((i % 1000) + 1) as i32,
            3 => (1000 - (i % 1000)) as i32,
            4 => {
                if i % 2 == 0 {
                    1
                } else {
                    1000
                }
            }
            5 => {
                let x = ((i * 37 + 13) % 1000) as i32 + 1;
                x
            }
            6 => {
                if i % 3 == 0 {
                    shelf_width.min(1000)
                } else {
                    1
                }
            }
            7 => rng.gen_range_i32(1, 1000),
            8 => {
                if i + 1 == n {
                    1000
                } else {
                    1
                }
            }
            9 => {
                let block = (i / 7) % 2;
                if block == 0 { 250 } else { 750 }
            }
            _ => ((i * i + 17) % 1000) as i32 + 1,
        };
        v.push(h);
        i += 1;
    }
    v
}

fn print_json_books(books: &[Vec<i32>], shelf_width: i32) {
    print!("{{\"books\":[");
    let mut i = 0usize;
    while i < books.len() {
        if i > 0 {
            print!(",");
        }
        print!("[{},{}]", books[i][0], books[i][1]);
        i += 1;
    }
    println!("],\"shelf_width\":{}}}", shelf_width);
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

    let mut t = 0usize;
    while t < total {
        let mode = t % modes;

        let shelf_width: i32 = match mode {
            0 => 1,
            1 => 1000,
            2 => 2,
            3 => 3,
            4 => 4,
            5 => 10,
            6 => 17,
            7 => 31,
            8 => 500,
            _ => rng.gen_range_i32(1, 1000),
        };

        let filler_len: usize = match mode {
            0 => 0,
            1 => 999,
            2 => 1,
            3 => 2,
            4 => 15,
            5 => 63,
            6 => 127,
            7 => 255,
            8 => 511,
            _ => rng.gen_range_usize(0, 999),
        };

        let special_thickness: i32 = match mode {
            0 => 1,
            1 => shelf_width,
            2 => 1,
            3 => shelf_width,
            4 => (shelf_width / 2).max(1),
            5 => 1,
            6 => shelf_width,
            7 => ((t % (shelf_width as usize)) as i32) + 1,
            8 => shelf_width,
            _ => rng.gen_range_i32(1, shelf_width),
        };

        let special_height: i32 = match mode {
            0 => 1,
            1 => 1000,
            2 => 1000,
            3 => 1,
            4 => 500,
            5 => ((t % 1000) as i32) + 1,
            6 => 999,
            7 => 2,
            8 => 777,
            _ => rng.gen_range_i32(1, 1000),
        };

        let fillers = make_fillers(filler_len, mode, shelf_width, &mut rng);
        let (books, sw) = Gen::generate_test_case(shelf_width, special_thickness, special_height, fillers);
        print_json_books(&books, sw);

        t += 1;
    }
}