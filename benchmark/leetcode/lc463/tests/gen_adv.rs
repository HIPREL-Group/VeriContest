use vstd::prelude::*;

verus! {

    pub open spec fn adjacent(r1: int, c1: int, r2: int, c2: int) -> bool {
        (r1 == r2 && (c1 + 1 == c2 || c2 + 1 == c1))
            || (c1 == c2 && (r1 + 1 == r2 || r2 + 1 == r1))
    }

    pub open spec fn is_land(grid: Seq<Vec<i32>>, rows: int, cols: int, r: int, c: int) -> bool {
        0 <= r < rows && 0 <= c < cols && grid[r][c] == 1
    }

    pub open spec fn reachable(grid: Seq<Vec<i32>>, rows: int, cols: int, r1: int, c1: int, r2: int, c2: int, fuel: nat) -> bool
        decreases fuel
    {
        if r1 == r2 && c1 == c2 {
            is_land(grid, rows, cols, r1, c1)
        } else if fuel == 0 {
            false
        } else {
            is_land(grid, rows, cols, r1, c1)
            && exists|r3: int, c3: int|
                adjacent(r1, c1, r3, c3)
                && is_land(grid, rows, cols, r3, c3)
                && reachable(grid, rows, cols, r3, c3, r2, c2, (fuel - 1) as nat)
        }
    }

    pub open spec fn exactly_one_island(grid: Seq<Vec<i32>>, rows: int, cols: int) -> bool {
        (exists|r: int, c: int| is_land(grid, rows, cols, r, c))
        && (forall|r1: int, c1: int, r2: int, c2: int|
            is_land(grid, rows, cols, r1, c1) && is_land(grid, rows, cols, r2, c2)
            ==> reachable(grid, rows, cols, r1, c1, r2, c2, (rows * cols) as nat))
    }

    pub open spec fn is_water(grid: Seq<Vec<i32>>, rows: int, cols: int, r: int, c: int) -> bool {
        0 <= r < rows && 0 <= c < cols && grid[r][c] == 0
    }

    pub open spec fn water_reachable(grid: Seq<Vec<i32>>, rows: int, cols: int, r1: int, c1: int, r2: int, c2: int, fuel: nat) -> bool
        decreases fuel
    {
        if r1 == r2 && c1 == c2 {
            is_water(grid, rows, cols, r1, c1)
        } else if fuel == 0 {
            false
        } else {
            is_water(grid, rows, cols, r1, c1)
            && exists|r3: int, c3: int|
                adjacent(r1, c1, r3, c3)
                && is_water(grid, rows, cols, r3, c3)
                && water_reachable(grid, rows, cols, r3, c3, r2, c2, (fuel - 1) as nat)
        }
    }

    pub open spec fn is_border_water(grid: Seq<Vec<i32>>, rows: int, cols: int, r: int, c: int) -> bool {
        is_water(grid, rows, cols, r, c) && (r == 0 || r == rows - 1 || c == 0 || c == cols - 1)
    }

    pub open spec fn no_lakes(grid: Seq<Vec<i32>>, rows: int, cols: int) -> bool {
        forall|r: int, c: int| is_water(grid, rows, cols, r, c) ==>
            exists|br: int, bc: int| is_border_water(grid, rows, cols, br, bc)
                && water_reachable(grid, rows, cols, r, c, br, bc, (rows * cols) as nat)
    }


pub open spec fn band_shape(grid: Seq<Vec<i32>>, rows: int, cols: int, lo: Seq<i32>, hi: Seq<i32>, spine: int) -> bool {
    1 <= rows <= 100 && 1 <= cols <= 100 && grid.len() == rows
    && lo.len() == rows && hi.len() == rows && 0 <= spine < cols
    && (forall|r: int| 0 <= r < rows ==> #[trigger] grid[r].len() == cols)
    && (forall|r: int| 0 <= r < rows ==> 0 <= #[trigger] lo[r] <= spine)
    && (forall|r: int| 0 <= r < rows ==> spine <= #[trigger] hi[r] < cols)
    && (forall|r: int, c: int| 0 <= r < rows && 0 <= c < cols ==>
        #[trigger] grid[r][c] == if lo[r] <= c <= hi[r] { 1i32 } else { 0i32 })
}
pub open spec fn delta(a: int, b: int) -> int { if a >= b { a - b } else { b - a } }
pub open spec fn band_distance(r1: int, c1: int, r2: int, c2: int, spine: int) -> int {
    if r1 == r2 { delta(c1, c2) } else { delta(c1, spine) + delta(r1, r2) + delta(c2, spine) }
}
proof fn band_land_path(grid: Seq<Vec<i32>>, rows: int, cols: int, lo: Seq<i32>, hi: Seq<i32>, spine: int,
    r1: int, c1: int, r2: int, c2: int, fuel: nat)
    requires band_shape(grid, rows, cols, lo, hi, spine),
        is_land(grid, rows, cols, r1, c1), is_land(grid, rows, cols, r2, c2),
        band_distance(r1, c1, r2, c2, spine) <= fuel,
    ensures reachable(grid, rows, cols, r1, c1, r2, c2, fuel),
    decreases fuel,
{
    if r1 != r2 || c1 != c2 {
        assert(fuel > 0);
        let nr = if r1 != r2 && c1 == spine { if r1 < r2 { r1 + 1 } else { r1 - 1 } } else { r1 };
        let nc = if r1 == r2 { if c1 < c2 { c1 + 1 } else { c1 - 1 } }
            else if c1 < spine { c1 + 1 } else if c1 > spine { c1 - 1 } else { c1 };
        assert(lo[nr] <= nc <= hi[nr]);
        assert(is_land(grid, rows, cols, nr, nc));
        assert(band_distance(nr, nc, r2, c2, spine) <= fuel - 1);
        band_land_path(grid, rows, cols, lo, hi, spine, nr, nc, r2, c2, (fuel - 1) as nat);
        assert(adjacent(r1, c1, nr, nc));
        assert(exists|r3: int, c3: int| adjacent(r1, c1, r3, c3)
            && is_land(grid, rows, cols, r3, c3)
            && reachable(grid, rows, cols, r3, c3, r2, c2, (fuel - 1) as nat));
    }
}
proof fn band_water_path(grid: Seq<Vec<i32>>, rows: int, cols: int, lo: Seq<i32>, hi: Seq<i32>, spine: int,
    r: int, c: int, border: int, fuel: nat)
    requires band_shape(grid, rows, cols, lo, hi, spine), is_water(grid, rows, cols, r, c),
        border == (if c < lo[r] { 0int } else { cols - 1 }), delta(c, border) <= fuel,
    ensures is_border_water(grid, rows, cols, r, border),
        water_reachable(grid, rows, cols, r, c, r, border, fuel),
    decreases fuel,
{
    if c != border {
        assert(fuel > 0);
        let nc = if c < lo[r] { c - 1 } else { c + 1 };
        assert(is_water(grid, rows, cols, r, nc));
        band_water_path(grid, rows, cols, lo, hi, spine, r, nc, border, (fuel - 1) as nat);
        assert(adjacent(r, c, r, nc));
        assert(exists|r3: int, c3: int| adjacent(r, c, r3, c3)
            && is_water(grid, rows, cols, r3, c3)
            && water_reachable(grid, rows, cols, r3, c3, r, border, (fuel - 1) as nat));
    }
}
proof fn band_is_valid(grid: Seq<Vec<i32>>, rows: int, cols: int, lo: Seq<i32>, hi: Seq<i32>, spine: int)
    requires band_shape(grid, rows, cols, lo, hi, spine),
    ensures exactly_one_island(grid, rows, cols), no_lakes(grid, rows, cols),
{
    assert(is_land(grid, rows, cols, 0, spine));
    assert forall|r1: int, c1: int, r2: int, c2: int|
        is_land(grid, rows, cols, r1, c1) && is_land(grid, rows, cols, r2, c2)
        implies reachable(grid, rows, cols, r1, c1, r2, c2, (rows * cols) as nat) by {
        if r1 == r2 {
            assert(cols - 1 <= rows * cols) by(nonlinear_arith) requires rows >= 1, cols >= 1;
        } else {
            assert(2 * (cols - 1) + rows - 1 <= rows * cols) by(nonlinear_arith)
                requires rows >= 2, cols >= 1;
        }
        band_land_path(grid, rows, cols, lo, hi, spine, r1, c1, r2, c2, (rows * cols) as nat);
    }
    assert forall|r: int, c: int| is_water(grid, rows, cols, r, c) implies
        exists|br: int, bc: int| is_border_water(grid, rows, cols, br, bc)
            && water_reachable(grid, rows, cols, r, c, br, bc, (rows * cols) as nat) by {
        let border = if c < lo[r] { 0int } else { cols - 1 };
        assert(cols - 1 <= rows * cols) by(nonlinear_arith) requires rows >= 1, cols >= 1;
        band_water_path(grid, rows, cols, lo, hi, spine, r, c, border, (rows * cols) as nat);
    }
}
pub fn generate_test_case(raw: Vec<Vec<i32>>) -> (grid: Vec<Vec<i32>>)
    ensures 1 <= grid.len() <= 100, 1 <= grid[0].len() <= 100,
        forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
        forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==>
            #[trigger] grid[i][j] == 0 || #[trigger] grid[i][j] == 1,
        exactly_one_island(grid@, grid.len() as int, grid[0].len() as int),
        no_lakes(grid@, grid.len() as int, grid[0].len() as int),
{
    let rows = if raw.len() == 0 { 1usize } else if raw.len() > 100 { 100usize } else { raw.len() };
    let cols = if raw.len() == 0 || raw[0].len() == 0 { 1usize }
        else if raw[0].len() > 100 { 100usize } else { raw[0].len() };
    let mut spine = cols / 2;
    let mut c = 0usize;
    while c < cols
        invariant c <= cols, 1 <= cols <= 100, spine < cols,
        decreases cols - c,
    {
        if raw.len() > 0 && c < raw[0].len() && raw[0][c] == 1 { spine = c; }
        c += 1;
    }
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut lows: Vec<i32> = Vec::new();
    let mut highs: Vec<i32> = Vec::new();
    let mut r = 0usize;
    while r < rows
        invariant r <= rows, 1 <= rows <= 100, 1 <= cols <= 100, spine < cols,
            grid.len() == r, lows.len() == r, highs.len() == r,
            forall|j: int| 0 <= j < r ==> #[trigger] grid[j].len() == cols,
            forall|j: int| 0 <= j < r ==> 0 <= #[trigger] lows[j] <= spine,
            forall|j: int| 0 <= j < r ==> spine <= #[trigger] highs[j] < cols,
            forall|j: int, k: int| 0 <= j < r && 0 <= k < cols ==>
                #[trigger] grid[j][k] == if lows[j] <= k <= highs[j] { 1i32 } else { 0i32 },
        decreases rows - r,
    {
        let mut low = spine;
        let mut high = spine;
        let mut c = 0usize;
        while c < cols
            invariant c <= cols, 1 <= cols <= 100, low <= spine <= high < cols,
            decreases cols - c,
        {
            if r < raw.len() && c < raw[r].len() && raw[r][c] == 1 {
                if c < low { low = c; }
                if c > high { high = c; }
            }
            c += 1;
        }
        let mut row: Vec<i32> = Vec::new();
        let mut c = 0usize;
        while c < cols
            invariant c <= cols, 1 <= cols <= 100, row.len() == c, low <= spine <= high < cols,
                forall|j: int| 0 <= j < c ==> #[trigger] row[j] == if low <= j <= high { 1i32 } else { 0i32 },
            decreases cols - c,
        {
            row.push(if low <= c && c <= high { 1 } else { 0 });
            c += 1;
        }
        lows.push(low as i32); highs.push(high as i32); grid.push(row);
        r += 1;
    }
    proof {
        assert(band_shape(grid@, rows as int, cols as int, lows@, highs@, spine as int));
        band_is_valid(grid@, rows as int, cols as int, lows@, highs@, spine as int);
    }
    grid
}


pub fn generate_candidate(rows: usize, cols: usize, bits: &Vec<Vec<u8>>) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= rows <= 100,
        1 <= cols <= 100,
        bits.len() == rows,
        forall|i: int| 0 <= i < rows ==> #[trigger] bits[i].len() == cols,
        forall|i: int, j: int| 0 <= i < rows && 0 <= j < cols ==>
            (#[trigger] bits[i][j] == 0u8 || #[trigger] bits[i][j] == 1u8),
        exists|i: int, j: int| 0 <= i < rows && 0 <= j < cols && #[trigger] bits[i][j] == 1u8,
    ensures
        1 <= grid.len() <= 100,
        grid.len() == rows,
        1 <= grid[0].len() <= 100,
        grid[0].len() == cols,
        forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
        forall|i: int, j: int|
            0 <= i < grid.len() && 0 <= j < grid[i].len() ==>
                #[trigger] grid[i][j] == 0 || #[trigger] grid[i][j] == 1,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            1 <= rows <= 100,
            1 <= cols <= 100,
            bits.len() == rows,
            0 <= i <= rows,
            grid.len() == i,
            forall|a: int| 0 <= a < rows ==> #[trigger] bits[a].len() == cols,
            forall|a: int, b: int| 0 <= a < rows && 0 <= b < cols ==>
                (#[trigger] bits[a][b] == 0u8 || #[trigger] bits[a][b] == 1u8),
            forall|a: int| 0 <= a < i as int ==> #[trigger] grid[a].len() == cols,
            forall|a: int, b: int| 0 <= a < i as int && 0 <= b < cols ==>
                (#[trigger] grid[a][b] == 0i32 || #[trigger] grid[a][b] == 1i32),
        decreases rows - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < cols
            invariant
                1 <= cols <= 100,
                bits.len() == rows,
                0 <= j <= cols,
                row.len() == j,
                i < rows,
                bits[i as int].len() == cols,
                forall|b: int| 0 <= b < cols ==>
                    (#[trigger] bits[i as int][b] == 0u8 || #[trigger] bits[i as int][b] == 1u8),
                forall|b: int| 0 <= b < j as int ==>
                    (#[trigger] row[b] == 0i32 || #[trigger] row[b] == 1i32),
            decreases cols - j,
        {
            let v: i32 = if bits[i][j] == 1u8 { 1 } else { 0 };
            row.push(v);
            j = j + 1;
        }
        grid.push(row);
        i = i + 1;
    }
    grid
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
    fn range(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn bit(&mut self, p: u64) -> u8 {
        if (self.next_u64() % 100) < p { 1 } else { 0 }
    }
}

fn make_bits(rows: usize, cols: usize, pattern: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let mut b: Vec<Vec<u8>> = Vec::with_capacity(rows);
    for i in 0..rows {
        let mut row = Vec::with_capacity(cols);
        for j in 0..cols {
            row.push(if pattern[i][j] == 1 { 1u8 } else { 0u8 });
        }
        b.push(row);
    }
    b
}

fn ensure_has_one(pattern: &mut Vec<Vec<u8>>, rows: usize, cols: usize) {
    let mut found = false;
    for i in 0..rows {
        for j in 0..cols {
            if pattern[i][j] == 1 {
                found = true;
            }
        }
    }
    if !found {
        pattern[0][0] = 1;
    }
}

// Flood fill to keep only the largest connected component
fn keep_one_island(pattern: &mut Vec<Vec<u8>>, rows: usize, cols: usize) {
    let mut visited = vec![vec![false; cols]; rows];
    let mut best: Vec<(usize,usize)> = Vec::new();
    for si in 0..rows {
        for sj in 0..cols {
            if pattern[si][sj] == 1 && !visited[si][sj] {
                let mut stack = vec![(si, sj)];
                let mut comp: Vec<(usize,usize)> = Vec::new();
                visited[si][sj] = true;
                while let Some((i, j)) = stack.pop() {
                    comp.push((i, j));
                    if i > 0 && pattern[i-1][j] == 1 && !visited[i-1][j] {
                        visited[i-1][j] = true;
                        stack.push((i-1, j));
                    }
                    if i+1 < rows && pattern[i+1][j] == 1 && !visited[i+1][j] {
                        visited[i+1][j] = true;
                        stack.push((i+1, j));
                    }
                    if j > 0 && pattern[i][j-1] == 1 && !visited[i][j-1] {
                        visited[i][j-1] = true;
                        stack.push((i, j-1));
                    }
                    if j+1 < cols && pattern[i][j+1] == 1 && !visited[i][j+1] {
                        visited[i][j+1] = true;
                        stack.push((i, j+1));
                    }
                }
                if comp.len() > best.len() {
                    best = comp;
                }
            }
        }
    }
    // Zero everything
    for i in 0..rows {
        for j in 0..cols {
            pattern[i][j] = 0;
        }
    }
    for &(i, j) in &best {
        pattern[i][j] = 1;
    }
    if best.is_empty() {
        pattern[0][0] = 1;
    }
}

// Fill any internal holes (water not connected to outside) to avoid "lakes"
fn fill_holes(pattern: &mut Vec<Vec<u8>>, rows: usize, cols: usize) {
    let mut reach = vec![vec![false; cols]; rows];
    let mut stack: Vec<(usize,usize)> = Vec::new();
    for i in 0..rows {
        if pattern[i][0] == 0 && !reach[i][0] {
            reach[i][0] = true;
            stack.push((i, 0));
        }
        if pattern[i][cols-1] == 0 && !reach[i][cols-1] {
            reach[i][cols-1] = true;
            stack.push((i, cols-1));
        }
    }
    for j in 0..cols {
        if pattern[0][j] == 0 && !reach[0][j] {
            reach[0][j] = true;
            stack.push((0, j));
        }
        if pattern[rows-1][j] == 0 && !reach[rows-1][j] {
            reach[rows-1][j] = true;
            stack.push((rows-1, j));
        }
    }
    while let Some((i, j)) = stack.pop() {
        if i > 0 && pattern[i-1][j] == 0 && !reach[i-1][j] {
            reach[i-1][j] = true;
            stack.push((i-1, j));
        }
        if i+1 < rows && pattern[i+1][j] == 0 && !reach[i+1][j] {
            reach[i+1][j] = true;
            stack.push((i+1, j));
        }
        if j > 0 && pattern[i][j-1] == 0 && !reach[i][j-1] {
            reach[i][j-1] = true;
            stack.push((i, j-1));
        }
        if j+1 < cols && pattern[i][j+1] == 0 && !reach[i][j+1] {
            reach[i][j+1] = true;
            stack.push((i, j+1));
        }
    }
    for i in 0..rows {
        for j in 0..cols {
            if pattern[i][j] == 0 && !reach[i][j] {
                pattern[i][j] = 1;
            }
        }
    }
}

fn sanitize(pattern: &mut Vec<Vec<u8>>, rows: usize, cols: usize) {
    ensure_has_one(pattern, rows, cols);
    keep_one_island(pattern, rows, cols);
    fill_holes(pattern, rows, cols);
    ensure_has_one(pattern, rows, cols);
}

fn gen_mode(rng: &mut Rng, mode: usize) -> (usize, usize, Vec<Vec<u8>>) {
    let (rows, cols) = match mode {
        0 => (1usize, 1usize),
        1 => (1, rng.range(1, 100)),
        2 => (rng.range(1, 100), 1),
        3 => (100, 100),
        4 => (rng.range(2, 10), rng.range(2, 10)),
        5 => (rng.range(1, 20), rng.range(1, 20)),
        6 => (rng.range(5, 50), rng.range(5, 50)),
        7 => (rng.range(1, 100), rng.range(1, 100)),
        8 => (50, 50),
        _ => (rng.range(1, 100), rng.range(1, 100)),
    };

    let mut pat = vec![vec![0u8; cols]; rows];

    match mode {
        0 => {
            pat[0][0] = 1;
        }
        3 => {
            // full grid
            for i in 0..rows {
                for j in 0..cols {
                    pat[i][j] = 1;
                }
            }
        }
        4 => {
            // single column of land in middle
            let c = cols / 2;
            for i in 0..rows {
                pat[i][c] = 1;
            }
        }
        6 => {
            // border rectangle
            let r1 = rows / 4;
            let r2 = (3 * rows) / 4;
            let c1 = cols / 4;
            let c2 = (3 * cols) / 4;
            for i in r1..=r2 {
                for j in c1..=c2 {
                    pat[i][j] = 1;
                }
            }
        }
        8 => {
            // diagonal-ish
            for i in 0..rows {
                let j = i.min(cols - 1);
                pat[i][j] = 1;
                if j + 1 < cols {
                    pat[i][j+1] = 1;
                }
            }
        }
        _ => {
            // random with connectivity via sanitizer
            let p = match mode {
                1 => 70,
                2 => 70,
                5 => 50,
                7 => 40,
                _ => 50,
            };
            for i in 0..rows {
                for j in 0..cols {
                    pat[i][j] = rng.bit(p as u64);
                }
            }
        }
    }

    sanitize(&mut pat, rows, cols);
    (rows, cols, pat)
}

fn print_json(grid: &[Vec<i32>]) {
    let grid = generate_test_case(grid.to_vec());
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
    } else { 1 };

    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let (rows, cols, pat) = gen_mode(&mut rng, mode);
        let bits = make_bits(rows, cols, &pat);
        let grid = generate_candidate(rows, cols, &bits);
        print_json(&grid);
    }
}
