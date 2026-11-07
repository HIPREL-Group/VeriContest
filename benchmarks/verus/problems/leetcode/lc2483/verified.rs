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

	proof fn lemma_score_step(customers: Seq<char>, i: int)
		requires
			0 <= i < customers.len(),
			forall |k: int| 0 <= k < customers.len() ==> customers[k] == 'Y' || customers[k] == 'N',
		ensures
			Self::score_prefix(customers, i + 1)
				== Self::score_prefix(customers, i)
					+ if customers[i] == 'Y' { 1int } else { -1int },
	{
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

		while i < len
			invariant
				1 <= customers@.len() <= 100_000,
				len == customers@.len(),
				forall |k: int| 0 <= k < customers@.len() ==> customers@[k] == 'Y' || customers@[k] == 'N',
				0 <= i <= len,
				score as int == Self::score_prefix(customers@, i as int),
				-(i as int) <= score as int <= i as int,
				0 <= best_hour <= i,
				best_score as int == Self::score_prefix(customers@, best_hour as int),
				forall |j: int| 0 <= j <= i as int ==> Self::score_prefix(customers@, j) <= best_score as int,
				forall |j: int| 0 <= j < best_hour as int ==> Self::score_prefix(customers@, j) < best_score as int,
			decreases len - i,
		{
			let ghost old_i: int = i as int;
			let ghost old_best_score: int = best_score as int;
			let c = customers.as_str().get_char(i);

			proof {
				Self::lemma_score_step(customers@, old_i);
			}

			if c == 'Y' {
				score = score + 1;
			} else {
				score = score - 1;
			}

			proof {
				assert(score as int == Self::score_prefix(customers@, old_i + 1));
				assert(-(old_i + 1) <= score as int <= old_i + 1);
			}

			if best_score < score {
				best_score = score;
				best_hour = i + 1;

				proof {
					assert(best_hour as int == old_i + 1);
					assert(best_score as int == Self::score_prefix(customers@, best_hour as int));
					assert(forall |j: int| 0 <= j <= old_i + 1 ==> Self::score_prefix(customers@, j) <= best_score as int) by {
						assert forall |j: int| 0 <= j <= old_i + 1 implies Self::score_prefix(customers@, j) <= best_score as int by {
							if j <= old_i {
								assert(Self::score_prefix(customers@, j) <= old_best_score);
								assert(old_best_score < best_score as int);
							} else {
								assert(j == old_i + 1);
								assert(Self::score_prefix(customers@, j) == best_score as int);
							}
						}
					};
					assert(forall |j: int| 0 <= j < best_hour as int ==> Self::score_prefix(customers@, j) < best_score as int) by {
						assert forall |j: int| 0 <= j < best_hour as int implies Self::score_prefix(customers@, j) < best_score as int by {
							assert(j <= old_i);
							assert(Self::score_prefix(customers@, j) <= old_best_score);
							assert(old_best_score < best_score as int);
						}
					};
				}
			} else {
				proof {
					assert(best_score as int == old_best_score);
					assert(forall |j: int| 0 <= j <= old_i + 1 ==> Self::score_prefix(customers@, j) <= best_score as int) by {
						assert forall |j: int| 0 <= j <= old_i + 1 implies Self::score_prefix(customers@, j) <= best_score as int by {
							if j <= old_i {
								assert(Self::score_prefix(customers@, j) <= best_score as int);
							} else {
								assert(j == old_i + 1);
								assert(Self::score_prefix(customers@, j) == score as int);
								assert(score as int <= best_score as int);
							}
						}
					};
				}
			}

			i = i + 1;
		}

		proof {
			assert(i == len);
			assert(0 <= best_hour as int <= customers@.len());
			assert(forall |j: int| 0 <= j <= customers@.len() ==> Self::score_prefix(customers@, j) <= Self::score_prefix(customers@, best_hour as int));
			assert(forall |j: int| 0 <= j < best_hour as int ==> Self::score_prefix(customers@, j) < Self::score_prefix(customers@, best_hour as int));
			assert(best_hour <= 100_000);
			assert(best_hour <= i32::MAX as usize);
		}

		best_hour as i32
	}
}

}
