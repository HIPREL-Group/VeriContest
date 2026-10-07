use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    ids: &Vec<i32>,
    ratings: &Vec<i32>,
    vegans: &Vec<i32>,
    prices: &Vec<i32>,
    distances: &Vec<i32>,
    vegan_friendly: i32,
    max_price: i32,
    max_distance: i32,
) -> (result: (Vec<Vec<i32>>, i32, i32, i32))
    requires
        1 <= ids.len() <= 10000,
        ids.len() == ratings.len(),
        ids.len() == vegans.len(),
        ids.len() == prices.len(),
        ids.len() == distances.len(),
        forall|i: int| 0 <= i < ids.len() ==> 1 <= #[trigger] ids[i] <= 100000,
        forall|i: int| 0 <= i < ratings.len() ==> 1 <= #[trigger] ratings[i] <= 100000,
        forall|i: int| 0 <= i < vegans.len() ==> (#[trigger] vegans[i] == 0 || vegans[i] == 1),
        forall|i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] <= 100000,
        forall|i: int| 0 <= i < distances.len() ==> 1 <= #[trigger] distances[i] <= 100000,
        forall|i: int, j: int| 0 <= i < j < ids.len() ==> ids[i] != ids[j],
        vegan_friendly == 0 || vegan_friendly == 1,
        1 <= max_price <= 100000,
        1 <= max_distance <= 100000,
    ensures
        ({
            let (restaurants, vf, mp, md) = result;
            &&& 1 <= restaurants.len() <= 10000
            &&& restaurants.len() == ids.len()
            &&& forall|i: int| #![trigger restaurants[i]]
                0 <= i < restaurants.len() ==> {
                    &&& restaurants[i].len() == 5
                    &&& 1 <= restaurants[i][0] <= 100000
                    &&& 1 <= restaurants[i][1] <= 100000
                    &&& (restaurants[i][2] == 0 || restaurants[i][2] == 1)
                    &&& 1 <= restaurants[i][3] <= 100000
                    &&& 1 <= restaurants[i][4] <= 100000
                }
            &&& vf == vegan_friendly
            &&& mp == max_price
            &&& md == max_distance
            &&& (vf == 0 || vf == 1)
            &&& 1 <= mp <= 100000
            &&& 1 <= md <= 100000
            &&& forall|i: int, j: int|
                0 <= i < j < restaurants.len()
                ==> restaurants[i][0] != restaurants[j][0]
        }),
{
    let n = ids.len();
    let mut restaurants: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n == ids.len(),
            ids.len() == ratings.len(),
            ids.len() == vegans.len(),
            ids.len() == prices.len(),
            ids.len() == distances.len(),
            1 <= n <= 10000,
            0 <= k <= n,
            restaurants.len() == k,
            forall|i: int| 0 <= i < ids.len() ==> 1 <= #[trigger] ids[i] <= 100000,
            forall|i: int| 0 <= i < ratings.len() ==> 1 <= #[trigger] ratings[i] <= 100000,
            forall|i: int| 0 <= i < vegans.len() ==> (#[trigger] vegans[i] == 0 || vegans[i] == 1),
            forall|i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] <= 100000,
            forall|i: int| 0 <= i < distances.len() ==> 1 <= #[trigger] distances[i] <= 100000,
            forall|i: int, j: int| 0 <= i < j < ids.len() ==> ids[i] != ids[j],
            forall|i: int| #![trigger restaurants[i]] 0 <= i < restaurants.len() ==> {
                &&& restaurants[i].len() == 5
                &&& restaurants[i][0] == ids[i]
                &&& restaurants[i][1] == ratings[i]
                &&& restaurants[i][2] == vegans[i]
                &&& restaurants[i][3] == prices[i]
                &&& restaurants[i][4] == distances[i]
            },
        decreases n - k,
    {
        let mut row: Vec<i32> = Vec::new();
        row.push(ids[k]);
        row.push(ratings[k]);
        row.push(vegans[k]);
        row.push(prices[k]);
        row.push(distances[k]);
        assert(row.len() == 5);
        assert(row[0] == ids[k as int]);
        assert(row[1] == ratings[k as int]);
        assert(row[2] == vegans[k as int]);
        assert(row[3] == prices[k as int]);
        assert(row[4] == distances[k as int]);
        restaurants.push(row);
        k = k + 1;
    }

    assert forall|i: int, j: int|
        0 <= i < j < restaurants.len()
        implies restaurants[i][0] != restaurants[j][0]
    by {
        assert(restaurants[i][0] == ids[i]);
        assert(restaurants[j][0] == ids[j]);
        assert(ids[i] != ids[j]);
    }

    (restaurants, vegan_friendly, max_price, max_distance)
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn unique_ids(rng: &mut Rng, n: usize) -> Vec<i32> {
    // Use a permutation-like approach via set check
    let mut ids: Vec<i32> = Vec::with_capacity(n);
    let mut used: std::collections::HashSet<i32> = std::collections::HashSet::new();
    while ids.len() < n {
        let v = rng.gen_range_i32(1, 100000);
        if !used.contains(&v) {
            used.insert(v);
            ids.push(v);
        }
    }
    ids
}

fn gen_vec_range(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v
}

fn gen_vegan(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push((rng.next_u64() % 2) as i32);
    }
    v
}

fn print_case(restaurants: &Vec<Vec<i32>>, vf: i32, mp: i32, md: i32) {
    print!("{{\"restaurants\":[");
    for (i, row) in restaurants.iter().enumerate() {
        if i > 0 { print!(","); }
        print!("[");
        for (j, x) in row.iter().enumerate() {
            if j > 0 { print!(","); }
            print!("{}", x);
        }
        print!("]");
    }
    println!("],\"vegan_friendly\":{},\"max_price\":{},\"max_distance\":{}}}", vf, mp, md);
}

fn build_and_print(
    rng: &mut Rng,
    n: usize,
    vf: i32,
    mp: i32,
    md: i32,
    vegan_all_one: bool,
    vegan_all_zero: bool,
    prices_all_low: bool,
    distances_all_low: bool,
    prices_all_high: bool,
    distances_all_high: bool,
) {
    let ids = unique_ids(rng, n);
    let ratings = gen_vec_range(rng, n, 1, 100000);
    let vegans = if vegan_all_one {
        vec![1i32; n]
    } else if vegan_all_zero {
        vec![0i32; n]
    } else {
        gen_vegan(rng, n)
    };
    let prices = if prices_all_low {
        gen_vec_range(rng, n, 1, 10)
    } else if prices_all_high {
        gen_vec_range(rng, n, 90000, 100000)
    } else {
        gen_vec_range(rng, n, 1, 100000)
    };
    let distances = if distances_all_low {
        gen_vec_range(rng, n, 1, 10)
    } else if distances_all_high {
        gen_vec_range(rng, n, 90000, 100000)
    } else {
        gen_vec_range(rng, n, 1, 100000)
    };

    let (restaurants, vf2, mp2, md2) =
        generate_test_case(&ids, &ratings, &vegans, &prices, &distances, vf, mp, md);
    print_case(&restaurants, vf2, mp2, md2);
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
    for t in 0..total {
        let mode = t % 10;
        match mode {
            0 => {
                // small random
                let n = rng.gen_range_usize(1, 10);
                let vf = (rng.next_u64() % 2) as i32;
                let mp = rng.gen_range_i32(1, 100000);
                let md = rng.gen_range_i32(1, 100000);
                build_and_print(&mut rng, n, vf, mp, md, false, false, false, false, false, false);
            }
            1 => {
                // n = 1
                let vf = (rng.next_u64() % 2) as i32;
                let mp = rng.gen_range_i32(1, 100000);
                let md = rng.gen_range_i32(1, 100000);
                build_and_print(&mut rng, 1, vf, mp, md, false, false, false, false, false, false);
            }
            2 => {
                // max size
                let vf = (rng.next_u64() % 2) as i32;
                let mp = rng.gen_range_i32(1, 100000);
                let md = rng.gen_range_i32(1, 100000);
                build_and_print(&mut rng, 10000, vf, mp, md, false, false, false, false, false, false);
            }
            3 => {
                // all vegan, vf=1
                let n = rng.gen_range_usize(5, 50);
                build_and_print(&mut rng, n, 1, 100000, 100000, true, false, false, false, false, false);
            }
            4 => {
                // no vegan, vf=1 -> empty filter
                let n = rng.gen_range_usize(5, 50);
                build_and_print(&mut rng, n, 1, 100000, 100000, false, true, false, false, false, false);
            }
            5 => {
                // max_price=1
                let n = rng.gen_range_usize(5, 100);
                build_and_print(&mut rng, n, 0, 1, 100000, false, false, false, false, false, false);
            }
            6 => {
                // max_distance=1
                let n = rng.gen_range_usize(5, 100);
                build_and_print(&mut rng, n, 0, 100000, 1, false, false, false, false, false, false);
            }
            7 => {
                // all low prices & distances
                let n = rng.gen_range_usize(5, 100);
                let vf = (rng.next_u64() % 2) as i32;
                build_and_print(&mut rng, n, vf, 100000, 100000, false, false, true, true, false, false);
            }
            8 => {
                // all high prices & distances, low max
                let n = rng.gen_range_usize(5, 100);
                build_and_print(&mut rng, n, 0, 50000, 50000, false, false, false, false, true, true);
            }
            9 => {
                // medium random
                let n = rng.gen_range_usize(100, 1000);
                let vf = (rng.next_u64() % 2) as i32;
                let mp = rng.gen_range_i32(1, 100000);
                let md = rng.gen_range_i32(1, 100000);
                build_and_print(&mut rng, n, vf, mp, md, false, false, false, false, false, false);
            }
            _ => {}
        }
    }
}