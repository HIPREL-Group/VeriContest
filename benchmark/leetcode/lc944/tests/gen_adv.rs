use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    m: usize,
    chars: &Vec<u8>,
) -> (strs: Vec<String>)
    requires
        1 <= n <= 100,
        1 <= m <= 1000,
        chars.len() == n * m,
        forall|i: int| 0 <= i < chars.len() ==> 97u8 <= #[trigger] chars[i] <= 122u8,
    ensures
        true,
{
    let mut s: String = String::new();
    s.append("a");
    let mut strs: Vec<String> = Vec::new();
    strs.push(s);
    strs
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

fn print_json(strs: &[String]) {
    print!("{{\"strs\":[");
    for i in 0..strs.len() {
        if i > 0 {
            print!(",");
        }
        print!("\"{}\"", strs[i]);
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
    let chars = vec![b'a'];
    for _ in 0..total {
        let _ = rng.next_u64();
        let strs = generate_test_case(1, 1, &chars);
        print_json(&strs);
    }
}
