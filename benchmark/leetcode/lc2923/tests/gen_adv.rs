use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    champ: usize,
    perm: &Vec<usize>,
) -> (grid: Vec<Vec<i32>>)
    requires
        2 <= n <= 100,
        champ < n,
        perm.len() == n,
        forall |i: int| 0 <= i < n as int ==> (#[trigger] perm[i]) < n,
        perm[champ as int] == 0,
        forall |i: int, j: int| 0 <= i < n as int && 0 <= j < n as int && i != j ==>
            (#[trigger] perm[i]) != (#[trigger] perm[j]),
    ensures
        2 <= grid.len() <= 100,
        grid.len() == n,
        forall |i: int| 0 <= i < grid.len() ==> (#[trigger] grid[i]).len() == grid.len(),
        forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid.len() ==>
            (#[trigger] grid[i][j] == 0 || grid[i][j] == 1),
        forall |i: int| 0 <= i < grid.len() ==> grid[i][i] == 0,
        forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid.len() && i != j ==>
            grid[i][j] + grid[j][i] == 1,
        Solution::is_champion(grid@, champ as int),
        exists |c: int| Solution::is_champion(grid@, c),
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == perm.len(),
            2 <= n <= 100,
            champ < n,
            perm[champ as int] == 0,
            forall |k: int| 0 <= k < n as int ==> (#[trigger] perm[k]) < n,
            forall |a: int, b: int| 0 <= a < n as int && 0 <= b < n as int && a != b ==>
                (#[trigger] perm[a]) != (#[trigger] perm[b]),
            i <= n,
            grid.len() == i,
            forall |r: int| 0 <= r < i as int ==> (#[trigger] grid[r]).len() == n as int,
            forall |r: int, c: int| 0 <= r < i as int && 0 <= c < n as int ==>
                (#[trigger] grid[r][c] == 0 || grid[r][c] == 1),
            forall |r: int| 0 <= r < i as int ==> grid[r][r] == 0,
            forall |r: int, c: int| 0 <= r < i as int && 0 <= c < n as int && r != c ==>
                grid[r][c] == (if perm[r] < perm[c] { 1int } else { 0int }),
        decreases n - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                n == perm.len(),
                i < n,
                j <= n,
                row.len() == j,
                forall |c: int| 0 <= c < j as int ==>
                    (#[trigger] row[c] == 0 || row[c] == 1),
                forall |c: int| 0 <= c < j as int && c != i as int ==>
                    row[c] == (if perm[i as int] < perm[c] { 1int } else { 0int }),
                forall |c: int| 0 <= c < j as int && c == i as int ==> row[c] == 0,
            decreases n - j,
        {
            if i == j {
                row.push(0);
            } else if perm[i] < perm[j] {
                row.push(1);
            } else {
                row.push(0);
            }
            j = j + 1;
        }
        grid.push(row);
        i = i + 1;
    }

    proof {
        assert forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid.len() && r != c
            implies grid[r][c] + grid[c][r] == 1
        by {
            assert(grid[r][c] == (if perm[r] < perm[c] { 1int } else { 0int }));
            assert(grid[c][r] == (if perm[c] < perm[r] { 1int } else { 0int }));
            assert(perm[r] != perm[c]);
        }

        assert forall |j: int| 0 <= j < grid.len() && j != champ as int
            implies #[trigger] grid[champ as int][j] == 1
        by {
            assert(grid[champ as int][j] == (if perm[champ as int] < perm[j] { 1int } else { 0int }));
            assert(perm[champ as int] == 0);
            assert(perm[j] < n);
            assert(perm[j] != 0);
        }

        assert(Solution::is_champion(grid@, champ as int));
    }

    grid
}

pub struct Solution;

impl Solution {
    pub open spec fn is_champion(grid: Seq<Vec<i32>>, c: int) -> bool {
        &&& 0 <= c < grid.len()
        &&& forall |j: int| 0 <= j < grid.len() && j != c ==> #[trigger] grid[c][j] == 1
    }
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
}

fn make_permutation(rng: &mut Rng, n: usize, champ: usize) -> Vec<usize> {
    // champ gets rank 0; others get ranks 1..n in some order
    let mut others: Vec<usize> = (0..n).filter(|&x| x != champ).collect();
    // Fisher-Yates shuffle
    for i in (1..others.len()).rev() {
        let j = rng.gen_range_usize(0, i);
        others.swap(i, j);
    }
    let mut perm = vec![0usize; n];
    perm[champ] = 0;
    for (rank, &idx) in others.iter().enumerate() {
        perm[idx] = rank + 1;
    }
    perm
}

fn generate_adversarial(rng: &mut Rng, mode: usize, t: usize) -> (usize, usize) {
    // returns (n, champ)
    let n = match mode {
        0 => 2,
        1 => 100,
        2 => 3,
        3 => 4 + (t % 10),
        4 => 50,
        5 => 99,
        6 => 10,
        7 => 2 + (t % 5),
        8 => 25 + (t % 20),
        9 => 100,
        _ => 2 + (t % 99),
    };
    let champ = match mode {
        0 => t % n,
        1 => 0,
        2 => n - 1,
        3 => rng.gen_range_usize(0, n - 1),
        4 => n / 2,
        5 => n - 1,
        6 => 0,
        7 => rng.gen_range_usize(0, n - 1),
        8 => rng.gen_range_usize(0, n - 1),
        9 => n - 1,
        _ => rng.gen_range_usize(0, n - 1),
    };
    (n, champ)
}

fn print_json(grid: &Vec<Vec<i32>>) {
    print!("{{\"grid\":[");
    for i in 0..grid.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..grid[i].len() {
            if j > 0 { print!(","); }
            print!("{}", grid[i][j]);
        }
        print!("]");
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, champ) = generate_adversarial(&mut rng, mode, t);
        let perm = make_permutation(&mut rng, n, champ);
        let grid = generate_test_case(n, champ, &perm);
        print_json(&grid);
    }
}