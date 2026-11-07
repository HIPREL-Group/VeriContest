use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
	pub open spec fn score_prefix(customers: Seq<char>, end: int) -> int
		recommends
			0 <= end <= customers.len(),
			forall |i: int| 0 <= i < customers.len() ==> customers[i] == 'Y' || customers[i] == 'N',
		decreases end,
	{
		if end <= 0 {
			0
		} else {
			Self::score_prefix(customers, end - 1)
				+ if customers[end - 1] == 'Y' { 1int } else { -1int }
		}
	}

	pub open spec fn is_best_closing_hour(customers: Seq<char>, h: int) -> bool {
		&&& 0 <= h <= customers.len()
		&&& forall |j: int| 0 <= j <= customers.len() ==> Self::score_prefix(customers, j) <= Self::score_prefix(customers, h)
		&&& forall |j: int| 0 <= j < h ==> Self::score_prefix(customers, j) < Self::score_prefix(customers, h)
	}

	pub fn best_closing_time(customers: String) -> (result: i32)
		requires
			1 <= customers@.len() <= 100_000,
			forall |i: int| 0 <= i < customers@.len() ==> customers@[i] == 'Y' || customers@[i] == 'N',
		ensures
			0 <= result as int <= customers@.len(),
			Self::is_best_closing_hour(customers@, result as int),
	{
		let len = customers.as_str().unicode_len();
		let mut i: usize = 0;
		let mut score: i32 = 0;
		let mut best_score: i32 = 0;
		let mut best_hour: usize = 0;

		while i < len {
			let c = customers.as_str().get_char(i);
			if c == 'Y' {
				score = score + 1;
			} else {
				score = score - 1;
			}
			if best_score < score {
				best_score = score;
				best_hour = i + 1;
			}
			i = i + 1;
		}

		best_hour as i32
	}
}

}
