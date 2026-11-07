use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    mat_flat: &Vec<i32>,
    target_flat: &Vec<i32>,
) -> (result: (Vec<Vec<i32>>, Vec<Vec<i32>>))
    requires
        1 <= n <= 10,
        mat_flat.len() == n * n,
        target_flat.len() == n * n,
        forall|i: int| 0 <= i < mat_flat.len() ==>
            (#[trigger] mat_flat[i] == 0 || mat_flat[i] == 1),
        forall|i: int| 0 <= i < target_flat.len() ==>
            (#[trigger] target_flat[i] == 0 || target_flat[i] == 1),
    ensures
        1 <= result.0@.len() <= 10,
        result.0@.len() == result.1@.len(),
        result.0@.len() == n,
        forall|i: int| 0 <= i < result.0@.len() ==> (#[trigger] result.0@[i])@.len() == result.0@.len(),
        forall|i: int| 0 <= i < result.1@.len() ==> (#[trigger] result.1@[i])@.len() == result.1@.len(),
        forall|i: int, j: int| 0 <= i < result.0@.len() && 0 <= j < result.0@.len() ==>
            (result.0@[i]@[j] == 0 || result.0@[i]@[j] == 1),
        forall|i: int, j: int| 0 <= i < result.1@.len() && 0 <= j < result.1@.len() ==>
            (result.1@[i]@[j] == 0 || result.1@[i]@[j] == 1),
{
    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            1 <= n <= 10,
            mat_flat.len() == n * n,
            i <= n,
            mat.len() == i,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] mat@[k])@.len() == n as int,
            forall|k: int, j: int| 0 <= k < i as int && 0 <= j < n as int ==>
                (mat@[k]@[j] == 0 || mat@[k]@[j] == 1),
            forall|idx: int| 0 <= idx < mat_flat.len() ==>
                (#[trigger] mat_flat[idx] == 0 || mat_flat[idx] == 1),
        decreases n - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                1 <= n <= 10,
                mat_flat.len() == n * n,
                i < n,
                j <= n,
                row.len() == j,
                forall|k: int| 0 <= k < j as int ==> (row@[k] == 0 || row@[k] == 1),
                forall|idx: int| 0 <= idx < mat_flat.len() ==>
                    (#[trigger] mat_flat[idx] == 0 || mat_flat[idx] == 1),
            decreases n - j,
        {
            assert(i * n + j < n * n) by (nonlinear_arith)
                requires i < n, j < n, n >= 1;
            let v = mat_flat[i * n + j];
            row.push(v);
            j = j + 1;
        }
        mat.push(row);
        i = i + 1;
    }

    let mut target: Vec<Vec<i32>> = Vec::new();
    let mut i2: usize = 0;
    while i2 < n
        invariant
            1 <= n <= 10,
            target_flat.len() == n * n,
            i2 <= n,
            target.len() == i2,
            forall|k: int| 0 <= k < i2 as int ==> (#[trigger] target@[k])@.len() == n as int,
            forall|k: int, j: int| 0 <= k < i2 as int && 0 <= j < n as int ==>
                (target@[k]@[j] == 0 || target@[k]@[j] == 1),
            forall|idx: int| 0 <= idx < target_flat.len() ==>
                (#[trigger] target_flat[idx] == 0 || target_flat[idx] == 1),
        decreases n - i2,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                1 <= n <= 10,
                target_flat.len() == n * n,
                i2 < n,
                j <= n,
                row.len() == j,
                forall|k: int| 0 <= k < j as int ==> (row@[k] == 0 || row@[k] == 1),
                forall|idx: int| 0 <= idx < target_flat.len() ==>
                    (#[trigger] target_flat[idx] == 0 || target_flat[idx] == 1),
            decreases n - j,
        {
            assert(i2 * n + j < n * n) by (nonlinear_arith)
                requires i2 < n, j < n, n >= 1;
            let v = target_flat[i2 * n + j];
            row.push(v);
            j = j + 1;
        }
        target.push(row);
        i2 = i2 + 1;
    }

    (mat, target)
}

} // verus!

struct Rng { state: u64 }
impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(1) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn range(&mut self, lo: usize, hi: usize) -> usize {
        let s = hi - lo + 1;
        lo + (self.next_u64() as usize % s)
    }
    fn bit(&mut self) -> i32 { (self.next_u64() & 1) as i32 }
}

fn rotate90(m: &Vec<Vec<i32>>, n: usize) -> Vec<Vec<i32>> {
    let mut r: Vec<Vec<i32>> = vec![vec![0; n]; n];
    for i in 0..n {
        for j in 0..n {
            r[j][n - 1 - i] = m[i][j];
        }
    }
    r
}

fn flatten(m: &Vec<Vec<i32>>) -> Vec<i32> {
    let mut f = Vec::new();
    for row in m.iter() {
        for &v in row.iter() { f.push(v); }
    }
    f
}

fn random_mat(rng: &mut Rng, n: usize) -> Vec<Vec<i32>> {
    let mut m = Vec::new();
    for _ in 0..n {
        let mut r = Vec::new();
        for _ in 0..n { r.push(rng.bit()); }
        m.push(r);
    }
    m
}

fn print_json(mat: &Vec<Vec<i32>>, target: &Vec<Vec<i32>>) {
    fn mstr(m: &Vec<Vec<i32>>) -> String {
        let mut s = String::from("[");
        for (i, row) in m.iter().enumerate() {
            if i > 0 { s.push(','); }
            s.push('[');
            for (j, v) in row.iter().enumerate() {
                if j > 0 { s.push(','); }
                s.push_str(&v.to_string());
            }
            s.push(']');
        }
        s.push(']');
        s
    }
    println!("{{\"mat\":{},\"target\":{}}}", mstr(mat), mstr(target));
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    for t in 0..total {
        let mode = t % 12;
        let n = match mode {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 10,
            _ => rng.range(1, 10),
        };

        let (mat, target) = match mode {
            0 => {
                // n=1 cases
                let a = rng.bit();
                let b = rng.bit();
                (vec![vec![a]], vec![vec![b]])
            }
            1 => {
                // random mat, target = rotation k
                let m = random_mat(&mut rng, n);
                let k = rng.range(0, 3);
                let mut r = m.clone();
                for _ in 0..k { r = rotate90(&r, n); }
                (m, r)
            }
            2 => {
                // identical
                let m = random_mat(&mut rng, n);
                (m.clone(), m)
            }
            3 => {
                // rotation 90
                let m = random_mat(&mut rng, n);
                let r = rotate90(&m, n);
                (m, r)
            }
            4 => {
                // rotation 180
                let m = random_mat(&mut rng, n);
                let r = rotate90(&rotate90(&m, n), n);
                (m, r)
            }
            5 => {
                // rotation 270
                let m = random_mat(&mut rng, n);
                let r = rotate90(&rotate90(&rotate90(&m, n), n), n);
                (m, r)
            }
            6 => {
                // all zeros
                (vec![vec![0; n]; n], vec![vec![0; n]; n])
            }
            7 => {
                // all ones
                (vec![vec![1; n]; n], vec![vec![1; n]; n])
            }
            8 => {
                // random unrelated
                (random_mat(&mut rng, n), random_mat(&mut rng, n))
            }
            9 => {
                // mat close to target but different by one cell
                let m = random_mat(&mut rng, n);
                let mut t = m.clone();
                let i = rng.range(0, n - 1);
                let j = rng.range(0, n - 1);
                t[i][j] = 1 - t[i][j];
                (m, t)
            }
            10 => {
                // identity-like
                let mut m = vec![vec![0; n]; n];
                for i in 0..n { m[i][i] = 1; }
                let k = rng.range(0, 3);
                let mut r = m.clone();
                for _ in 0..k { r = rotate90(&r, n); }
                (m, r)
            }
            _ => {
                // single one
                let mut m = vec![vec![0; n]; n];
                let i = rng.range(0, n - 1);
                let j = rng.range(0, n - 1);
                m[i][j] = 1;
                let k = rng.range(0, 3);
                let mut r = m.clone();
                for _ in 0..k { r = rotate90(&r, n); }
                (m, r)
            }
        };

        let mf = flatten(&mat);
        let tf = flatten(&target);
        let (m, tg) = generate_test_case(n, &mf, &tf);
        print_json(&m, &tg);
    }
}