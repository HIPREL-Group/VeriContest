use vstd::prelude::*;

verus! {

pub fn construct_rows(raw: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    ensures
        1 <= result.len() <= 200,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == 2,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i][0] <= 1000 && 1 <= result[i][1] <= 1000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i][0] < #[trigger] result[j][0],
{
    let count = if raw.len() == 0 { 1usize } else if raw.len() > 200 { 200usize } else { raw.len() };
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;
    let mut previous = 0i32;
    while i < count
        invariant
            1 <= count <= 200, 0 <= i <= count, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j].len() == 2,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j][0] <= 1000 && 1 <= result[j][1] <= 1000,
            0 <= previous <= 1000 - count as int + i as int,
            i > 0 ==> result[i - 1][0] == previous,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> #[trigger] result[j][0] < #[trigger] result[k][0],
        decreases count - i,
    {
        let a = if i < raw.len() && raw[i].len() > 0 { raw[i][0] } else { 1 };
        let b = if i < raw.len() && raw[i].len() > 1 { raw[i][1] } else { 1 };
        let mut a = if a < 1 { 1 } else if a > 1000 { 1000 } else { a };
        let mut b = if b < 1 { 1 } else if b > 1000 { 1000 } else { b };
        let upper = 1000 - count as i32 + i as i32 + 1;
        let v = a;
        let v = if v > upper { upper } else { v };
        let v = if v <= previous { previous + 1 } else { v };
        a = v;
        assert forall|j: int| 0 <= j < result.len() implies result[j][0] < v by {
            if j < i - 1 { assert(result[j][0] < result[(i - 1) as int][0]); }
        }
        previous = v;
        let mut row = Vec::new();
        row.push(a);
        row.push(b);
        result.push(row);
        i += 1;
    }
    result
}

pub fn generate_test_case(nums1: Vec<Vec<i32>>, nums2: Vec<Vec<i32>>) -> (result: (Vec<Vec<i32>>, Vec<Vec<i32>>))
    ensures
        1 <= result.0.len() <= 200,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == 2,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i][0] <= 1000 && 1 <= result.0[i][1] <= 1000,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> #[trigger] result.0[i][0] < #[trigger] result.0[j][0],
        1 <= result.1.len() <= 200,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i].len() == 2,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i][0] <= 1000 && 1 <= result.1[i][1] <= 1000,
        forall|i: int, j: int| 0 <= i < j < result.1.len() ==> #[trigger] result.1[i][0] < #[trigger] result.1[j][0],
{
    (construct_rows(nums1), construct_rows(nums2))
}


pub fn generate_candidate(
    ids1: &Vec<i32>,
    vals1: &Vec<i32>,
    ids2: &Vec<i32>,
    vals2: &Vec<i32>,
) -> (result: (Vec<Vec<i32>>, Vec<Vec<i32>>))
    requires
        ids1.len() == vals1.len(),
        ids2.len() == vals2.len(),
        1 <= ids1.len() <= 200,
        1 <= ids2.len() <= 200,
        forall|i: int| 0 <= i < ids1.len() ==> 1 <= #[trigger] ids1[i] <= 1000,
        forall|i: int| 0 <= i < vals1.len() ==> 1 <= #[trigger] vals1[i] <= 1000,
        forall|i: int| 0 <= i < ids2.len() ==> 1 <= #[trigger] ids2[i] <= 1000,
        forall|i: int| 0 <= i < vals2.len() ==> 1 <= #[trigger] vals2[i] <= 1000,
    ensures
        1 <= result.0.len() <= 200,
        1 <= result.1.len() <= 200,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == 2,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i].len() == 2,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i][0] <= 1000 && 1 <= result.0[i][1] <= 1000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i][0] <= 1000 && 1 <= result.1[i][1] <= 1000,
{
    let mut nums1: Vec<Vec<i32>> = Vec::new();
    let mut nums2: Vec<Vec<i32>> = Vec::new();

    let n1 = ids1.len();
    let mut i: usize = 0;
    while i < n1
        invariant
            n1 == ids1.len(),
            ids1.len() == vals1.len(),
            0 <= i <= n1,
            nums1.len() == i,
            1 <= ids1.len() <= 200,
            forall|k: int| 0 <= k < ids1.len() ==> 1 <= #[trigger] ids1[k] <= 1000,
            forall|k: int| 0 <= k < vals1.len() ==> 1 <= #[trigger] vals1[k] <= 1000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums1[k].len() == 2,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums1[k][0] <= 1000 && 1 <= nums1[k][1] <= 1000,
        decreases n1 - i,
    {
        let mut entry: Vec<i32> = Vec::new();
        entry.push(ids1[i]);
        entry.push(vals1[i]);
        assert(entry.len() == 2);
        assert(entry[0] == ids1[i as int]);
        assert(entry[1] == vals1[i as int]);
        nums1.push(entry);
        i = i + 1;
    }

    let n2 = ids2.len();
    let mut j: usize = 0;
    while j < n2
        invariant
            n2 == ids2.len(),
            ids2.len() == vals2.len(),
            0 <= j <= n2,
            nums2.len() == j,
            1 <= ids2.len() <= 200,
            forall|k: int| 0 <= k < ids2.len() ==> 1 <= #[trigger] ids2[k] <= 1000,
            forall|k: int| 0 <= k < vals2.len() ==> 1 <= #[trigger] vals2[k] <= 1000,
            forall|k: int| 0 <= k < j as int ==> #[trigger] nums2[k].len() == 2,
            forall|k: int| 0 <= k < j as int ==> 1 <= #[trigger] nums2[k][0] <= 1000 && 1 <= nums2[k][1] <= 1000,
        decreases n2 - j,
    {
        let mut entry: Vec<i32> = Vec::new();
        entry.push(ids2[j]);
        entry.push(vals2[j]);
        assert(entry.len() == 2);
        nums2.push(entry);
        j = j + 1;
    }

    (nums1, nums2)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(1) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as usize)
    }
}

fn build_sorted_unique_ids(rng: &mut Rng, n: usize, min_id: i32, max_id: i32) -> Vec<i32> {
    // Choose n distinct ids in [min_id, max_id], sorted ascending
    let range_size = (max_id - min_id + 1) as usize;
    let n_actual = if n > range_size { range_size } else { n };
    let mut chosen: std::collections::BTreeSet<i32> = std::collections::BTreeSet::new();
    let mut attempts = 0;
    while chosen.len() < n_actual && attempts < n_actual * 20 {
        let v = rng.gen_range(min_id, max_id);
        chosen.insert(v);
        attempts += 1;
    }
    // Fill if still short
    let mut v = min_id;
    while chosen.len() < n_actual && v <= max_id {
        chosen.insert(v);
        v += 1;
    }
    chosen.into_iter().collect()
}

fn gen_vals(rng: &mut Rng, n: usize) -> Vec<i32> {
    (0..n).map(|_| rng.gen_range(1, 1000)).collect()
}

fn mode_test(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>, Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // Small arrays, disjoint ids
            let ids1 = vec![1, 2, 3];
            let ids2 = vec![4, 5, 6];
            let v1 = gen_vals(rng, 3);
            let v2 = gen_vals(rng, 3);
            (ids1, v1, ids2, v2)
        }
        1 => {
            // All overlapping ids
            let ids = vec![1, 2, 3, 4, 5];
            let v1 = gen_vals(rng, 5);
            let v2 = gen_vals(rng, 5);
            (ids.clone(), v1, ids, v2)
        }
        2 => {
            // Single element each
            let id1 = rng.gen_range(1, 1000);
            let id2 = rng.gen_range(1, 1000);
            (vec![id1], vec![rng.gen_range(1, 1000)], vec![id2], vec![rng.gen_range(1, 1000)])
        }
        3 => {
            // Max length both
            let ids1 = build_sorted_unique_ids(rng, 200, 1, 1000);
            let ids2 = build_sorted_unique_ids(rng, 200, 1, 1000);
            let v1 = gen_vals(rng, ids1.len());
            let v2 = gen_vals(rng, ids2.len());
            (ids1, v1, ids2, v2)
        }
        4 => {
            // One small, one max
            let ids1 = vec![500];
            let ids2 = build_sorted_unique_ids(rng, 200, 1, 1000);
            (ids1, vec![rng.gen_range(1, 1000)], ids2.clone(), gen_vals(rng, ids2.len()))
        }
        5 => {
            // Min/max values
            let ids1 = vec![1, 1000];
            let ids2 = vec![1, 1000];
            (ids1, vec![1, 1000], ids2, vec![1000, 1])
        }
        6 => {
            // Interleaved ids
            let ids1: Vec<i32> = (1..=20).filter(|x| x % 2 == 1).collect();
            let ids2: Vec<i32> = (1..=20).filter(|x| x % 2 == 0).collect();
            let v1 = gen_vals(rng, ids1.len());
            let v2 = gen_vals(rng, ids2.len());
            (ids1, v1, ids2, v2)
        }
        7 => {
            // nums1 ids all less than nums2 ids
            let ids1: Vec<i32> = (1..=10).collect();
            let ids2: Vec<i32> = (500..=510).collect();
            let v1 = gen_vals(rng, ids1.len());
            let v2 = gen_vals(rng, ids2.len());
            (ids1, v1, ids2, v2)
        }
        8 => {
            // Same single id
            let id = rng.gen_range(1, 1000);
            (vec![id], vec![rng.gen_range(1, 1000)], vec![id], vec![rng.gen_range(1, 1000)])
        }
        9 => {
            // Random sizes, random ids
            let n1 = rng.gen_usize(1, 50);
            let n2 = rng.gen_usize(1, 50);
            let ids1 = build_sorted_unique_ids(rng, n1, 1, 1000);
            let ids2 = build_sorted_unique_ids(rng, n2, 1, 1000);
            let v1 = gen_vals(rng, ids1.len());
            let v2 = gen_vals(rng, ids2.len());
            (ids1, v1, ids2, v2)
        }
        _ => {
            let n1 = rng.gen_usize(1, 200);
            let n2 = rng.gen_usize(1, 200);
            let ids1 = build_sorted_unique_ids(rng, n1, 1, 1000);
            let ids2 = build_sorted_unique_ids(rng, n2, 1, 1000);
            let v1 = gen_vals(rng, ids1.len());
            let v2 = gen_vals(rng, ids2.len());
            (ids1, v1, ids2, v2)
        }
    }
}

fn print_json(nums1: &[Vec<i32>], nums2: &[Vec<i32>]) {
    let (nums1, nums2) = generate_test_case(nums1.to_vec(), nums2.to_vec());
    print!("{{\"nums1\":[");
    for (i, e) in nums1.iter().enumerate() {
        if i > 0 { print!(","); }
        print!("[{},{}]", e[0], e[1]);
    }
    print!("],\"nums2\":[");
    for (i, e) in nums2.iter().enumerate() {
        if i > 0 { print!(","); }
        print!("[{},{}]", e[0], e[1]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    for t in 0..total {
        let mode = t % 11;
        let (ids1, v1, ids2, v2) = mode_test(&mut rng, mode);
        if ids1.is_empty() || ids2.is_empty() || ids1.len() > 200 || ids2.len() > 200 {
            continue;
        }
        let mut ok = true;
        for &x in &ids1 { if x < 1 || x > 1000 { ok = false; } }
        for &x in &ids2 { if x < 1 || x > 1000 { ok = false; } }
        for &x in &v1 { if x < 1 || x > 1000 { ok = false; } }
        for &x in &v2 { if x < 1 || x > 1000 { ok = false; } }
        if !ok { continue; }
        let (nums1, nums2) = generate_candidate(&ids1, &v1, &ids2, &v2);
        print_json(&nums1, &nums2);
    }
}
