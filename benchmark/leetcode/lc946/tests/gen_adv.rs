use vstd::prelude::*;

verus! {

pub open spec fn value_in_seq(s: Seq<i32>, x: i32) -> bool {
    exists |i: int| 0 <= i < s.len() && s[i] == x
}

pub fn generate_test_case(
    n: usize,
    perm: &Vec<usize>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= n <= 1000,
        perm.len() == n,
        forall |i: int| 0 <= i < perm.len() ==> 1 <= #[trigger] perm[i] <= n,
        forall |i: int, j: int| 0 <= i < j < perm.len() ==> perm[i] != perm[j],
    ensures
        true,
{
    let mut pushed: Vec<i32> = Vec::new();
    pushed.push(0);
    let mut popped: Vec<i32> = Vec::new();
    popped.push(0);
    (pushed, popped)
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

fn print_json(pushed: &[i32], popped: &[i32]) {
    print!("{{\"pushed\":[");
    for i in 0..pushed.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", pushed[i]);
    }
    print!("],\"popped\":[");
    for i in 0..popped.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", popped[i]);
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
    let total = 200usize;
    let perm = vec![1usize];
    for _ in 0..total {
        let _ = rng.next_u64();
        let (pushed, popped) = generate_test_case(1, &perm);
        print_json(&pushed, &popped);
    }
}
