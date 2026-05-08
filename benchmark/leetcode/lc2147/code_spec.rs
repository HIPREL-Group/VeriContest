use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seat_count_prefix(s: Seq<char>, n: int) -> int
        decreases n
    {
        if n <= 0 {
            0int
        } else {
            Self::seat_count_prefix(s, n - 1) + if s[n - 1] == 'S' { 1int } else { 0int }
        }
    }

    pub open spec fn plants_prefix(s: Seq<char>, n: int) -> int
        decreases n
    {
        if n <= 0 {
            0int
        } else {
            let prev_seats = Self::seat_count_prefix(s, n - 1);
            if s[n - 1] == 'P' && prev_seats >= 2 && prev_seats % 2 == 0 {
                Self::plants_prefix(s, n - 1) + 1
            } else {
                0int
            }
        }
    }

    pub open spec fn ways_prefix(s: Seq<char>, n: int) -> int
        decreases n
    {
        if n <= 0 {
            1
        } else {
            let prev = Self::ways_prefix(s, n - 1);
            let prev_seats = Self::seat_count_prefix(s, n - 1);
            if s[n - 1] == 'S' && prev_seats >= 2 && prev_seats % 2 == 0 {
                (prev * (Self::plants_prefix(s, n - 1) + 1)) % 1_000_000_007
            } else {
                prev
            }
        }
    }

    pub open spec fn number_of_ways_spec(s: Seq<char>) -> int {
        let seats = Self::seat_count_prefix(s, s.len() as int);
        if seats == 0 || seats % 2 == 1 {
            0
        } else {
            Self::ways_prefix(s, s.len() as int)
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn number_of_ways(corridor: String) -> (result: i32)
        requires
            1 <= corridor@.len() <= 100_000,
            forall |i: int| 0 <= i < corridor@.len() ==> corridor@[i] == 'S' || corridor@[i] == 'P',
        ensures
            0 <= result < 1_000_000_007,
            result as int == Self::number_of_ways_spec(corridor@),
    {
        let mod_num: u128 = 1_000_000_007;
        let len = corridor.as_str().unicode_len();
        let mut seat_count: usize = 0;
        let mut plants: usize = 0;
        let mut ways: u128 = 1;
        let mut i: usize = 0;

        while i < len {
            let c = corridor.as_str().get_char(i);
            if c == 'S' {
                if seat_count >= 2 && seat_count % 2 == 0 {
					let sep = plants + 1;
					let prod = ways * sep as u128;
					let new_ways = prod % mod_num;
					ways = new_ways;
                }
                seat_count += 1;
                plants = 0;
            } else {
                if seat_count >= 2 && seat_count % 2 == 0 {
                    plants += 1;
                }
            }
            i += 1;
        }

        if seat_count == 0 || seat_count % 2 == 1 {
            0
        } else {
            ways as i32
        }
    }
}

}
