use vstd::prelude::*;

verus! {

// We generate a tree by giving each node i (for i >= 2) a parent p[i-2] in [1, i-1].
// Edges are (p[i-2], i) for i = 2..=n.

pub fn generate_test_case(
    n: usize,
    parents: &Vec<usize>,
) -> (res: (usize, Vec<usize>, Vec<usize>))
    requires
        2 <= n <= 100000,
        parents.len() == n - 1,
        forall|i: int| 0 <= i < parents.len() ==> 1 <= #[trigger] parents[i] <= i + 1,
    ensures
        res.0 == n,
        res.1.len() == n - 1,
        res.2.len() == n - 1,
        1 <= res.0 <= 100000,
        forall|j: int| 0 <= j < n - 1 ==> 1 <= #[trigger] res.1@[j] <= n,
        forall|j: int| 0 <= j < n - 1 ==> 1 <= #[trigger] res.2@[j] <= n,
{
    let mut u_edges: Vec<usize> = Vec::new();
    let mut v_edges: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n - 1
        invariant
            2 <= n <= 100000,
            parents.len() == n - 1,
            forall|k: int| 0 <= k < parents.len() ==> 1 <= #[trigger] parents[k] <= k + 1,
            0 <= i <= n - 1,
            u_edges.len() == i,
            v_edges.len() == i,
            forall|k: int| 0 <= k < i ==> 1 <= #[trigger] u_edges@[k] <= n,
            forall|k: int| 0 <= k < i ==> 1 <= #[trigger] v_edges@[k] <= n,
        decreases n - 1 - i,
    {
        let p = parents[i];
        let c = i + 2;
        assert(1 <= p <= i + 1);
        assert(c <= n);
        u_edges.push(p);
        v_edges.push(c);
        i = i + 1;
    }
    (n, u_edges, v_edges)
}

}

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_mul(2862933555777941757).wrapping_add(3037000493) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        if lo >= hi { return lo; }
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn build_parents(rng: &mut Rng, n: usize, mode: usize) -> Vec<usize> {
    // parents[i] in [1, i+1], for i = 0..n-2 (representing node i+2's parent)
    let mut p: Vec<usize> = Vec::with_capacity(n - 1);
    match mode {
        0 => {
            // Path: node i+2's parent is i+1
            for i in 0..n - 1 {
                p.push(i + 1);
            }
        }
        1 => {
            // Star: node i+2's parent is 1
            for _ in 0..n - 1 {
                p.push(1);
            }
        }
        2 => {
            // Caterpillar / random
            for i in 0..n - 1 {
                p.push(rng.gen_range(1, i + 1));
            }
        }
        3 => {
            // Two stars joined: first half parent=1, second half parent=2
            for i in 0..n - 1 {
                let node = i + 2;
                if node == 2 {
                    p.push(1);
                } else if i < (n - 1) / 2 {
                    p.push(1);
                } else {
                    p.push(2);
                }
            }
        }
        4 => {
            // Balanced-ish binary: parent is (node/2)
            for i in 0..n - 1 {
                let node = i + 2;
                let par = node / 2;
                p.push(par);
            }
        }
        5 => {
            // Path from node 1: 1-2-3-...-n
            for i in 0..n - 1 {
                p.push(i + 1);
            }
        }
        6 => {
            // Random but biased to small parents (star-like)
            for i in 0..n - 1 {
                let r = rng.gen_range(0, 3);
                if r == 0 {
                    p.push(1);
                } else {
                    p.push(rng.gen_range(1, i + 1));
                }
            }
        }
        7 => {
            // "Y" shape: one long chain with a branch
            for i in 0..n - 1 {
                let node = i + 2;
                if node == n && n > 3 {
                    p.push(2);
                } else {
                    p.push(i + 1);
                }
            }
        }
        8 => {
            // Spider: center 1 with multiple legs
            let legs = 4.min(n - 1);
            for i in 0..n - 1 {
                if i < legs {
                    p.push(1);
                } else {
                    // extend one leg
                    let leg = (i - legs) % legs;
                    let base = 2 + leg;
                    // just chain onto leg nodes
                    p.push(if i + 1 >= base + legs { i + 1 - legs } else { base });
                    // ensure p[i] <= i+1; fallback
                    let last = *p.last().unwrap();
                    if last > i + 1 {
                        p.pop();
                        p.push(i + 1);
                    } else if last < 1 {
                        p.pop();
                        p.push(1);
                    }
                }
            }
        }
        _ => {
            for i in 0..n - 1 {
                p.push(rng.gen_range(1, i + 1));
            }
        }
    }
    // Safety clamp
    for i in 0..p.len() {
        if p[i] < 1 { p[i] = 1; }
        if p[i] > i + 1 { p[i] = i + 1; }
    }
    p
}

fn print_json(n: usize, u_edges: &[usize], v_edges: &[usize]) {
    print!("{{\"n\":{},\"u_edges\":[", n);
    for i in 0..u_edges.len() {
        if i > 0 { print!(","); }
        print!("{}", u_edges[i]);
    }
    print!("],\"v_edges\":[");
    for i in 0..v_edges.len() {
        if i > 0 { print!(","); }
        print!("{}", v_edges[i]);
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
    let modes = 9usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 2 + (t % 20),
            1 => 3 + (t % 50),
            2 => 5 + (t % 200),
            3 => 4 + (t % 30),
            4 => 7 + (t % 100),
            5 => 2 + (t % 10),
            6 => 50 + (t % 500),
            7 => 6 + (t % 40),
            8 => 10 + (t % 100),
            _ => 20,
        };
        let n = if n < 2 { 2 } else if n > 1000 { 1000 } else { n };
        let parents = build_parents(&mut rng, n, mode);
        let (nn, u, v) = generate_test_case(n, &parents);
        print_json(nn, &u, &v);
    }
}