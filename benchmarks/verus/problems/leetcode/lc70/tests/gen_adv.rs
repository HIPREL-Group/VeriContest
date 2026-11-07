use vstd::prelude::*;

verus! {

pub open spec fn fib_spec(n: nat) -> nat
    decreases n
{
    if n <= 0 { 
        0 
    } else if n == 1 { 
        1 
    } else { 
        fib_spec((n - 2) as nat) + fib_spec((n - 1) as nat) 
    }
}

// Proof helper: fib is monotonically non-decreasing
pub proof fn fib_monotone(a: nat, b: nat)
    requires a <= b
    ensures fib_spec(a) <= fib_spec(b)
    decreases b
{
    if b == 0 {
    } else if b == 1 {
        if a == 0 {
        }
    } else {
        if a == b {
        } else {
            fib_monotone(a, (b - 1) as nat);
        }
    }
}

// Prove fib_spec(46) <= i32::MAX (fib(46) = 1836311903, i32::MAX = 2147483647)
pub proof fn fib_46_bound()
    ensures fib_spec(46) <= i32::MAX
{
    // Compute fib step by step
    assert(fib_spec(0) == 0) by { reveal_with_fuel(fib_spec, 1); }
    assert(fib_spec(1) == 1) by { reveal_with_fuel(fib_spec, 1); }
    assert(fib_spec(2) == 1) by { reveal_with_fuel(fib_spec, 3); }
    assert(fib_spec(3) == 2) by { reveal_with_fuel(fib_spec, 4); }
    assert(fib_spec(4) == 3) by { reveal_with_fuel(fib_spec, 5); }
    assert(fib_spec(5) == 5) by { reveal_with_fuel(fib_spec, 6); }
    assert(fib_spec(6) == 8) by { reveal_with_fuel(fib_spec, 7); }
    assert(fib_spec(7) == 13) by { reveal_with_fuel(fib_spec, 8); }
    assert(fib_spec(8) == 21) by { reveal_with_fuel(fib_spec, 9); }
    assert(fib_spec(9) == 34) by { reveal_with_fuel(fib_spec, 10); }
    assert(fib_spec(10) == 55) by { reveal_with_fuel(fib_spec, 11); }
    assert(fib_spec(11) == 89) by { reveal_with_fuel(fib_spec, 12); }
    assert(fib_spec(12) == 144) by { reveal_with_fuel(fib_spec, 13); }
    assert(fib_spec(13) == 233) by { reveal_with_fuel(fib_spec, 14); }
    assert(fib_spec(14) == 377) by { reveal_with_fuel(fib_spec, 15); }
    assert(fib_spec(15) == 610) by { reveal_with_fuel(fib_spec, 16); }
    assert(fib_spec(16) == 987) by { reveal_with_fuel(fib_spec, 17); }
    assert(fib_spec(17) == 1597) by { reveal_with_fuel(fib_spec, 18); }
    assert(fib_spec(18) == 2584) by { reveal_with_fuel(fib_spec, 19); }
    assert(fib_spec(19) == 4181) by { reveal_with_fuel(fib_spec, 20); }
    assert(fib_spec(20) == 6765) by { reveal_with_fuel(fib_spec, 21); }
    assert(fib_spec(21) == 10946) by { reveal_with_fuel(fib_spec, 22); }
    assert(fib_spec(22) == 17711) by { reveal_with_fuel(fib_spec, 23); }
    assert(fib_spec(23) == 28657) by { reveal_with_fuel(fib_spec, 24); }
    assert(fib_spec(24) == 46368) by { reveal_with_fuel(fib_spec, 25); }
    assert(fib_spec(25) == 75025) by { reveal_with_fuel(fib_spec, 26); }
    assert(fib_spec(26) == 121393) by { reveal_with_fuel(fib_spec, 27); }
    assert(fib_spec(27) == 196418) by { reveal_with_fuel(fib_spec, 28); }
    assert(fib_spec(28) == 317811) by { reveal_with_fuel(fib_spec, 29); }
    assert(fib_spec(29) == 514229) by { reveal_with_fuel(fib_spec, 30); }
    assert(fib_spec(30) == 832040) by { reveal_with_fuel(fib_spec, 31); }
    assert(fib_spec(31) == 1346269) by { reveal_with_fuel(fib_spec, 32); }
    assert(fib_spec(32) == 2178309) by { reveal_with_fuel(fib_spec, 33); }
    assert(fib_spec(33) == 3524578) by { reveal_with_fuel(fib_spec, 34); }
    assert(fib_spec(34) == 5702887) by { reveal_with_fuel(fib_spec, 35); }
    assert(fib_spec(35) == 9227465) by { reveal_with_fuel(fib_spec, 36); }
    assert(fib_spec(36) == 14930352) by { reveal_with_fuel(fib_spec, 37); }
    assert(fib_spec(37) == 24157817) by { reveal_with_fuel(fib_spec, 38); }
    assert(fib_spec(38) == 39088169) by { reveal_with_fuel(fib_spec, 39); }
    assert(fib_spec(39) == 63245986) by { reveal_with_fuel(fib_spec, 40); }
    assert(fib_spec(40) == 102334155) by { reveal_with_fuel(fib_spec, 41); }
    assert(fib_spec(41) == 165580141) by { reveal_with_fuel(fib_spec, 42); }
    assert(fib_spec(42) == 267914296) by { reveal_with_fuel(fib_spec, 43); }
    assert(fib_spec(43) == 433494437) by { reveal_with_fuel(fib_spec, 44); }
    assert(fib_spec(44) == 701408733) by { reveal_with_fuel(fib_spec, 45); }
    assert(fib_spec(45) == 1134903170) by { reveal_with_fuel(fib_spec, 46); }
    assert(fib_spec(46) == 1836311903) by { reveal_with_fuel(fib_spec, 47); }
}

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        1 <= n <= 45,
    ensures
        1 <= res <= 45,
        fib_spec((res + 1) as nat) <= i32::MAX,
{
    proof {
        fib_46_bound();
        fib_monotone((n + 1) as nat, 46nat);
    }
    n
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
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
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

    // Adversarial fixed values
    let adversarial: [i32; 15] = [1, 2, 3, 4, 5, 10, 20, 30, 40, 43, 44, 45, 15, 25, 35];

    for t in 0..total {
        let n: i32 = if t < adversarial.len() {
            adversarial[t]
        } else {
            let mode = t % 5;
            match mode {
                0 => 1,
                1 => 45,
                2 => rng.gen_range_i32(1, 10),
                3 => rng.gen_range_i32(35, 45),
                _ => rng.gen_range_i32(1, 45),
            }
        };
        let v = generate_test_case(n);
        println!("{{\"n\":{}}}", v);
    }
}